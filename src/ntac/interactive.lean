import ntac.ntac

open tactic
open interactive (parse)
open tactic.interactive ( cases_arg_p propagate_tags)
open interactive.types (texpr location using_ident with_ident_list only_flag)
open lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace ntac
--meta def trace_state {α : Type}
namespace interactive
/- meta def induction2 :
  parse tactic.interactive.cases_arg_p →
  parse interactive.types.using_ident →
  parse interactive.types.with_ident_list →
  parse (optional (lean.parser.tk "generalizing" *> lean.parser.many lean.parser.ident)) → ntac unit
:= henkan tactic.interactive.induction -/

meta def getgoal1 : ntac expr := 
do g::_ ← henkan get_goals,
return g

meta def getgoal1_or_done : ntac gost := 
do gs ← henkan get_goals,
return $ match gs with
| g::_ := gost.unres g
| _ :=gost.done
end
-- meta def exact (e : expr) (md := semireducible) : ntac unit := 
-- do tg ← getgoal1,
--    ret ← henkan $ tactic.exact e md,
--    kata ← henkan (infer_type e),
--    replc_ntac tg (gost.exact e)
meta def exact (e : expr) (md := semireducible) : ntac unit := 
do tg ← getgoal1,
   henkan $ tactic.exact e md

meta def admit : ntac unit :=
henkan target >>= exact ∘ expr.mk_sorry

meta def skiptgt : ntac unit :=
do hg ← getgoal1,
replc_ntac hg $ gost.skip $ gost.unres hg

meta def «sorry» : ntac unit := admit

meta def induction (hp : parse cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (optional (tk "generalizing" *> lean.parser.many lean.parser.ident))) : ntac unit := 
  henkan $ tactic.interactive.induction hp rec_name ids revert

meta def aa : ntac unit :=
fail "assumption tactic failed"

meta def get_gost_expr_list (goals : list(name × expr)): ntac (list (gost × expr)) :=
do
goal2 ← goals.mfilter $ λ ⟨n, m⟩, bnot <$> (henkan $ is_assigned m),
goal2type ← henkan $ monad.sequence $ list.map (λ nex:name × expr, infer_type nex.2) goal2 ,
let goal2unres := list.map (λ nex:name × expr, gost.unres $ nex.2) goal2 in
return $  list.zip goal2unres goal2type

-- meta def assumption2 : ntac unit :=
-- henkan1 "assum" tactic.interactive.assumption

private meta def concat_tags (tac : ntac (list (name × expr))) : ntac unit :=
let s := (do in_tag ← henkan get_main_tag,
      r ← tac,
      /- remove assigned metavars -/
      r ← r.mfilter $ λ ⟨n, m⟩, bnot <$> (henkan $ is_assigned m),
      match r with
      | [(_, m)] := henkan $ set_tag m in_tag /- if there is only new subgoal, we just propagate `in_tag` -/
      | _        := r.mmap' (λ ⟨n, m⟩, henkan $ set_tag m (n::in_tag))
      end) in
mcond (henkan tags_enabled)
  s
  (tac >> henkan skip)

meta def assumption : ntac unit :=
do { ctx ← henkan local_context,
     tg ← getgoal1,
     t   ← henkan target,
     H   ← henkan $ find_same_type t ctx,
     ty ← henkan $ infer_type H,
     replc_ntac tg (gost.assumption t),--t janakute ty?
     exact H}
<|> fail "assumption tactic failed"

meta def rw (q : parse interactive.rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit := do tg ← getgoal1, replc_ntac tg $ gost.rewrite $ gost.unres tg,henkan $ interactive.rw q l cfg
meta def delta (q : parse ident*) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit := henkan $ interactive.delta q l
meta def simp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : ntac unit := 
              do tg ← getgoal1,
               henkan $ interactive.simp use_iota_eqn no_dflt hs attr_names locat cfg,
               ng ← getgoal1_or_done,
               replc_ntac tg $ gost.simp ng

meta def apply (q : parse texpr) : ntac unit := 
do tg ← getgoal1,
  h ← henkan $ i_to_expr_for_apply q,
  goals ← henkan $ tactic.apply h,
  glist ← get_gost_expr_list goals,
  replc_ntac tg $ gost.apply h glist,
  --henkan $ interactive.concat_tags $ henkan2 $ return goals,
  concat_tags $ return goals


meta def rsimp : ntac unit := do tg ← getgoal1, 
henkan $ tactic.rsimp,tg2 ← getgoal1,replc_ntac tg $ gost.simp $ gost.unres tg2


@[inline] meta def readmy : ntac format :=
λ s, 
let (tac, str) := s in
result.success (to_fmt str) s

@[inline] meta def read2 : ntac tactic_state :=
λ s, let (tac, str) := s in
  result.success tac s

meta def pp {α} [has_to_tactic_format α] (a:α) : ntac format :=
henkan $ has_to_tactic_format.to_tactic_format a

meta def trace {α} [has_to_tactic_format α] (a : α) : ntac unit :=
do fmt ← pp a,
   return $ _root_.trace_fmt fmt (λ u, ())

meta def trace_state : ntac unit := 
do s ← readmy,
   s2 ← read2,
   trace $ s ++ "\n------\n" ++ (to_fmt s2)
meta def aua := trace "fg"
meta def trace_state2 : ntac unit := henkan tactic.interactive.trace_state

meta def split : ntac unit :=
do tg ← getgoal1,
goals ← henkan $ tactic.split,
glist ← get_gost_expr_list goals,
let gost_new := gost.apply tg glist in 
do replc_ntac tg gost_new,
  concat_tags $ return goals


-- meta def seq'2 (tac1 : ntac unit) (tac2 : ntac unit) : ntac unit :=
-- henkan1 "vovo" $ do g::gs ← get_goals,
--    set_goals [g],
--    henkan2 tac1,
--    all_goals' $ henkan2 tac2,
--    gs' ← get_goals,
--    set_goals (gs' ++ gs)

meta def seq' (tac1 : ntac unit) (tac2 : ntac unit) : ntac unit :=
do g::gs ← henkan get_goals,
   gosts_bak ← get_gost,
   henkan $ set_goals [g],
   set_gost $ gost.unres g,
   tac1,
   gosts ← get_gost,
   goals ← henkan get_goals,
   set_gost $ let l := list.map (λ e, (e,gost.unres e)) goals in gost.andthen gosts l,
   all_goals' tac2,
   gosts_new ← get_gost,
   gs' ← henkan get_goals,
   henkan $ set_goals (gs' ++ gs),
   set_gost $ replc_unres g gosts_new gosts_bak

meta instance : has_andthen (ntac unit) (ntac unit) (ntac unit) :=
⟨seq'⟩

meta def rotate_left (n: nat): ntac unit:= henkan $ tactic.rotate_left n 
end interactive
end ntac

#check tactic.interactive.induction


