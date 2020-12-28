import ntac.goal_tree
-- @[reducible] meta def ntac := tactic

@[reducible] meta def ntac := interaction_monad (tactic_state × goal_info)

open tactic----------------------------------------------------------------------------------------------------------------------------------------------------
namespace ntac

meta def henkan {α} (t: tactic α): ntac α :=
λ ts,
let (tac, str) := ts in 
let res := t tac in
match res with 
| (result.success a s)       := (result.success a (s,str)) 
| (result.exception t ref s) := (result.exception t ref (s,str))
end

meta def henkan_inv {α} (t: ntac α) : tactic α :=
do g::_ ← get_goals,
type ← infer_type g,
kind ← infer_type type,
let info := type_info.mk type kind in
let goaltree := goal_tree.unres g in
let goal_info2 := goal_info.mk info goaltree in
λ sa,
let res := t (sa, goal_info2) in
match res with 
| (result.success a s)       := (result.success a s.1) 
| (result.exception t ref s) := (result.exception t ref s.1)
end

meta def change_goal_info (f:goal_info → goal_info) : ntac unit := 
λ sa,
let (tst, str) := sa in
result.success () (tst, f str)

meta def set_goal_info (g: goal_info) : ntac unit :=
λ sa,
let (tst, _) := sa in
result.success () (tst, g)

meta def get_goal_info: ntac goal_info := 
λ sa,
let (tst, str) := sa in result.success str (tst, str)

meta def replc_ntac (e:expr) (g: goal_tree) := change_goal_info $ replc_unres e g
meta def replc_head (e:expr) (g: goal_tree) := change_goal_info $ replc_unres e g

meta instance : interactive.executor ntac :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, henkan_inv }

meta instance : has_to_tactic_format expr :=
⟨tactic_format_expr⟩

meta instance : alternative ntac :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _,
  ..interaction_monad.monad }

meta def step {α} (c : ntac α) : ntac unit := do gs ← henkan get_goals,c >>return ()

meta def istep {α} (line0 col0 : ℕ) (line col : ℕ) (t : ntac α) : ntac unit :=
λ s, (@scope_trace _ line col (λ _, step t s)).clamp_pos line0 line col

meta def save_info (p : pos) : ntac unit := henkan $ tactic.save_info p
 
meta def execute (c : ntac unit) : ntac unit := c

meta def fail {α} {β} [has_to_format β] (msg : β) : ntac α :=
  interaction_monad.fail msg
meta def first {α} : list (ntac α) → ntac α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

meta def solve1 {α} (tac : ntac α) : ntac α :=
do gs ← henkan get_goals,
   match gs with
   | []      := fail "solve1 tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do henkan $ set_goals [g],
        a ← tac,
        gs' ← henkan $ get_goals,
        match gs' with
        | [] := henkan $ set_goals rs >> pure a
        | gs := fail "solve1 tactic failed, focused goal has not been solved"
        end
   end

meta def solve {α} (ts : list (ntac α)) : ntac α := first $ list.map solve1 ts

--meta def trace_state {α : Type}

private meta def all_goals'_core (tac : ntac unit) : list expr → list expr → ntac unit
| []        ac := henkan $ set_goals ac
| (g :: gs) ac :=
  mcond ( henkan $ is_assigned g) (all_goals'_core gs ac) $
    do henkan $ set_goals [g],
       tac,
       new_gs ←  henkan $ get_goals,
       all_goals'_core gs (ac ++ new_gs)

/-- Apply the given tactic to all goals. -/
meta def all_goals' (tac : ntac unit) : ntac unit :=
do gs ←  henkan $ get_goals,
   all_goals'_core tac gs []

meta def skip : ntac unit :=
result.success ()


meta def try {α}(t : ntac α) : ntac unit := λ s,
match t s with
| (result.exception _ _ _) := result.success () s
| (result.success _ s') := result.success () s'
end
end ntac
