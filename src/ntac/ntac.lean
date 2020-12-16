-- @[reducible] meta def ntac := tactic
def mkprf := list string → string
meta def test (o: interaction_monad string (list string)): interaction_monad string string :=
do sdt::_ ← o,
let s := sdt in
 return s

meta def list2monad {α} {β} [monad β] : list (β α) → β (list α) :=
λ k,
match k with
| [] := return []
| h::r := 
let rrr := r in
do hh ← h,
rr ← list2monad rrr,
pure (hh::rr)
end

meta inductive gost : Type
| unres : expr → gost
| exact : expr → gost
| assumption : expr → gost
| rewrite : gost → gost
| simp : gost → gost
| skip : gost → gost
| admit : gost
| done : gost
| apply : expr → list (gost × expr) → gost
| case : list (gost × expr) → gost
| init : list (gost × expr) → gost
| andthen : gost →list (expr × gost) → gost
| unres_andthen : expr → gost

-- meta def juststr (s: string): gost := gost.tact [([], λ _,s)]
-- meta def gost1 (g: gost) (f: string → string): gost := gost.tact [g] (λ p, 
-- match p with 
-- | h::[]  := f h
-- |_ := "error!"
-- end)
-- meta def addtact (g: gost) (s: string) := gost1 g (λ st, st ++ s)

meta def replc_unres :expr → gost → gost → gost := 
λ e g_new g_org,
match g_org with
| gost.unres e2 := if e = e2 then g_new else g_org
| gost.unres_andthen e2 := if e = e2 then g_new else g_org
| gost.skip g := gost.skip $ replc_unres e g_new g
| gost.simp g := gost.skip $ replc_unres e g_new g
| gost.case gl := gost.case $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| gost.init gl := gost.init $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| gost.apply ee gl := gost.apply ee $ list.map (λ p,let (a, b):= p in ((replc_unres e g_new) a, b)) gl
| gost.andthen g gl := gost.andthen g $ list.map (λ p,let (a, b):= p in (a, (replc_unres e g_new) b)) gl
| _ := g_org
end

meta def initgoals (gl: list expr): mkprf := 
λ lst1, 
let lst := list.zip_with (λ a b, to_string a ++ "\n" ++ b) gl lst1 in
let gls := list.foldl (λ a b, a ++ "\n" ++ b) "initial goals:" lst in
gls

@[reducible] meta def ntac := interaction_monad (tactic_state × gost)


-- @[reducible] meta def ntac := (interaction_monad tactic_state) × string
open tactic----------------------------------------------------------------------------------------------------------------------------------------------------
namespace ntac

meta def gost_to_string : gost → string :=
λ g, match g with
| gost.unres e :=  " *unres* :"++e.to_string
| gost.unres_andthen e :=  " *unres andthen* :"++e.to_string
| gost.admit := "sorry"
| gost.done := "done"
| gost.exact e:= "exact " ++e.to_string 
| gost.assumption e:= "assumption " ++e.to_string 
| gost.rewrite g:= "rw (" ++ gost_to_string g ++")"
| gost.simp g:= "simp (" ++ gost_to_string g ++")"
| gost.skip g:= "skip (" ++ gost_to_string g ++ ")"
| gost.apply ee gl := 
let sl := @list.map (gost × expr) string (λ p, let (a, b) := p in "("++(to_string b) ++":" ++(gost_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) ("apply <" ++ee.to_string ++"> and from[") sl in
str ++ "]"
| gost.case gl := 
let sl := @list.map (gost × expr) string (λ p, let (a, b) := p in "("++(to_string b) ++":" ++(gost_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) "case[" sl in
str ++ "]"
  
| gost.init gl := 
let sl := @list.map (gost × expr) string (λ p, let (a, b) := p in "("++(to_string b) ++":" ++(gost_to_string a)++")") gl in
let str := list.foldl (λ acc s, acc ++", "++ s) "init[" sl in
str ++ "]"
| gost.andthen tac1 tac2 :=
let str1 := gost_to_string tac1 in
let sl := @list.map (expr × gost) string (λ p, let (a, b) := p in "("++(to_string a) ++" → " ++(gost_to_string b)++")") tac2 in
let str := list.foldl (λ acc s, acc ++", "++ s) ("do {"++str1++"} and then{") sl in
str ++ "}"
end

meta def for_andthen : gost → gost :=
λ g, match g with
| gost.unres e := gost.unres_andthen e
| _ := g
end

meta instance : has_to_format gost :=
⟨λ g,to_fmt $ gost_to_string g⟩


meta def henkan {α} (t: tactic α): ntac α :=
λ ts,
let tac := ts.1 in 
let res := t tac in
let str := ts.2 in
match res with 
| (result.success a s)       := (result.success a (s, str)) 
| (result.exception t ref s) := (result.exception t ref (s,gost.admit))
end

-- meta def henkan1 {α} (s_add: string) (t: tactic α) : ntac α :=
-- λ ts,
-- let tac := ts.1 in 
-- let res := t tac in
-- let str := ts.2 in
-- match res with 
-- | (result.success a s)       := (result.success a (s, (addtact str s_add)))
-- | (result.exception t ref s) := (result.exception t ref (s,gost.admit))
-- end

-- meta def henkan1_base {α} (s_add: list string → string) (t: tactic α) : ntac α :=
-- λ ts,
-- let tac := ts.1 in 
-- let res := t tac in
-- let str := ts.2 in
-- match res with 
-- | (result.success a s)       := (result.success a (s, (gost.tact [str] s_add)))
-- | (result.exception t ref s) := (result.exception t ref (s,gost.admit))
-- end



meta def henkan2 {α} (t: ntac α) : tactic α :=
do goals ← get_goals,
exprs ← monad.sequence $ list.map infer_type goals,
let goals_gost := list.map gost.unres goals in
λ sa,
let res := t (sa, gost.init $ list.zip goals_gost exprs) in
match res with 
| (result.success a s)       := (result.success a s.1) 
| (result.exception t ref s) := (result.exception t ref s.1)
end

-- meta def adddd {α}  (s_add: string) (a:α) : ntac α := 
-- λ sa,
-- let (tst, str) := sa in
-- result.success a (tst, addtact str s_add)


meta def change_gost (f:gost → gost) : ntac unit := 
λ sa,
let (tst, str) := sa in
result.success () (tst, f str)

meta def set_gost (g: gost) : ntac unit :=
λ sa,
let (tst, _) := sa in
result.success () (tst, g)

meta def get_gost: ntac gost := 
λ sa,
let (tst, str) := sa in result.success str (tst, str)

meta def replc_ntac (e:expr) (g: gost) := change_gost $ replc_unres e g


meta instance : interactive.executor ntac :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, henkan2 }

meta instance : has_to_tactic_format expr :=
⟨tactic_format_expr⟩

meta instance : alternative ntac :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _,
  ..interaction_monad.monad }
--meta instance : monad ntac := by delta ntac; apply_instance

--meta instance : alternative ntac := by delta ntac; apply_instance

meta def step {α} (c : ntac α) : ntac unit := 
do gs ← henkan get_goals,
c >>return ()
--c >> adddd ("\n<"++gs.to_string++">\n") ()

meta def istep {α} (line0 col0 : ℕ) (line col : ℕ) (t : ntac α) : ntac unit :=
λ s, (@scope_trace _ line col (λ _, step t s)).clamp_pos line0 line col

meta def save_info (p : pos) : ntac unit :=
henkan $ tactic.save_info p
 
meta def execute (c : ntac unit) : ntac unit := 
c

meta def fail {α} {β} [has_to_format β] (msg : β) : ntac α :=
  interaction_monad.fail msg
meta def first {α} : list (ntac α) → ntac α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

meta def solve1 {α} (tac : ntac α) : ntac α :=
do 
--aa::as ← pure ([] : list string),
gs ← henkan get_goals,
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

end ntac
