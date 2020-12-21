import ntac.ntac
import tactic.ring
import tactic.ring_exp
import tactic.wlog
import tactic.norm_num
open tactic
open interactive (parse)
open tactic.interactive ( cases_arg_p rw_rules obtain_parse ring.mode)
open interactive.types (texpr location using_ident with_ident_list only_flag ident_ pexpr_list_or_texpr)
open lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many
local prefix `#`:0 := ntac.henkan

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
do g::_ ← # get_goals,
return g

meta def getgoal1_or_done : ntac goal_tree := 
do gs ← henkan get_goals,
return $ match gs with
| g::_ := goal_tree.unres g
| _ :=goal_tree.done
end
-- meta def exact (e : expr) (md := semireducible) : ntac unit := 
-- do tg ← getgoal1,
--    ret ← # tactic.exact e md,
--    kata ← henkan (infer_type e),
--    replc_ntac tg (goal_tree.exact e)
meta def skiptgt : ntac unit :=
do hg ← getgoal1,
replc_ntac hg $ goal_tree.skip $ goal_tree.unres hg

meta def exact (q : parse texpr) : ntac unit :=
do tg ← getgoal1,
tgt : expr ← # target,
   e ← # i_to_expr_strict ``(%%q : %%tgt),
   # tactic.exact e,
   kata ← # infer_type e,
   replc_ntac tg (goal_tree.exact e)

meta def «from» := exact
meta def admit : ntac unit :=
#  target >>= tactic.exact ∘ expr.mk_sorry


meta def «sorry» : ntac unit := admit

meta def induction (hp : parse cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (optional (tk "generalizing" *> lean.parser.many lean.parser.ident))) : ntac unit := 
  # tactic.interactive.induction hp rec_name ids revert

meta def aa : ntac unit :=
fail "assumption tactic failed"

meta def get_goal_tree_expr_list (goals : list(name × expr)): ntac (list (goal_tree × expr)) :=
do
goal2 ← goals.mfilter $ λ ⟨n, m⟩, bnot <$> (# is_assigned m),
goal2type ← # monad.sequence $ list.map (λ nex:name × expr, infer_type nex.2) goal2 ,
let goal2unres := list.map (λ nex:name × expr, goal_tree.unres $ nex.2) goal2 in
return $ list.zip goal2unres goal2type

-- meta def assumption2 : ntac unit :=
-- henkan1 "assum" tactic.interactive.assumption

private meta def concat_tags (tac : ntac (list (name × expr))) : ntac unit :=
let s := (do in_tag ← henkan get_main_tag,
      r ← tac,
      /- remove assigned metavars -/
      r ← r.mfilter $ λ ⟨n, m⟩, bnot <$> (# is_assigned m),
      match r with
      | [(_, m)] := # set_tag m in_tag /- if there is only new subgoal, we just propagate `in_tag` -/
      | _        := r.mmap' (λ ⟨n, m⟩, # set_tag m (n::in_tag))
      end) in
mcond (henkan tags_enabled)
  s
  (tac >> skip)

meta def assumption : ntac unit :=
do { ctx ← henkan local_context,
     tg ← getgoal1,
     t   ← henkan target,
     H   ← # find_same_type t ctx,
     ty ← # infer_type H,
     replc_ntac tg (goal_tree.assumption t),--t janakute ty?
     # tactic.exact H}
<|> fail "assumption tactic failed"

meta def rw (q : parse interactive.rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit := do tg ← getgoal1, replc_ntac tg $ goal_tree.rewrite $ goal_tree.unres tg,# interactive.rw q l cfg
meta def delta (q : parse ident*) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit := # interactive.delta q l
meta def simp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : ntac unit := 
              do tg ← getgoal1,
              --(all_hyps, s, u) ← # mk_simp_set_core no_dflt attr_names hs tt,
              --(hss, gex, hex, all_hyps) ← # decode_simp_arg_list_with_symm hs,
              --gg ← # monad.sequence $ list.map (λ pe, tactic.to_expr pe tt ff) $ list.map prod.fst hss,
              # interactive.simp use_iota_eqn no_dflt hs attr_names locat cfg,
              ng ← getgoal1_or_done,
              replc_ntac tg $ goal_tree.simp ng
meta def simpa (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : ntac unit := # interactive.simpa use_iota_eqn no_dflt hs attr_names tgt cfg

meta def rewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit :=
 do tg ← getgoal1,
 # interactive.rewrite q l cfg,
    ng ← getgoal1_or_done,
    replc_ntac tg $ goal_tree.simp ng

meta def rwa (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit :=
rewrite q l cfg >> try assumption

meta def apply_mycore (e : expr) (cfg : apply_cfg := {}) : ntac (list (name × expr)) := 
do tg ← getgoal1,
  goals ← # tactic.apply e,
  glist ← get_goal_tree_expr_list goals,
  replc_ntac tg $ goal_tree.apply tg glist,
  return goals
  --# interactive.concat_tags $ henkan2 $ return goals,


meta def apply  (q : parse texpr) : ntac unit :=
concat_tags (do h ← # i_to_expr_for_apply q, apply_mycore h)
meta def tact_eapply (e : expr) : ntac (list (name × expr)) :=
apply_mycore e {new_goals := new_goals.non_dep_only}
meta def eapply (q : parse texpr) : ntac unit :=
concat_tags (henkan (i_to_expr_for_apply q) >>= tact_eapply)

meta def by_cases : parse cases_arg_p → ntac unit
| (n, q) := concat_tags $ do
  p ← # tactic.to_expr_strict q,
  # tactic.by_cases p (n.get_or_else `h),
  pos_g :: neg_g :: rest ← henkan get_goals,
  return [(`pos, pos_g), (`neg, neg_g)]

meta def rsimp : ntac unit := do tg ← getgoal1, 
# tactic.rsimp,tg2 ← getgoal1,replc_ntac tg $ goal_tree.simp $ goal_tree.unres tg2


@[inline] meta def readmy : ntac format :=
λ s, 
let (tac, str) := s in
result.success (to_fmt str) s

@[inline] meta def read2 : ntac tactic_state :=
λ s, let (tac, str) := s in
  result.success tac s

meta def pp {α} [has_to_tactic_format α] (a:α) : ntac format :=
# has_to_tactic_format.to_tactic_format a

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
goals ← # tactic.split,
glist ← get_goal_tree_expr_list goals,
let goal_tree_new := goal_tree.apply tg glist in 
do replc_ntac tg goal_tree_new,
  concat_tags $ return goals

meta def intro2_core (n : name) : ntac expr :=
do tg ← getgoal1,
 e ← # intro_core n,
 te ← # infer_type e,
 ng ← getgoal1,
replc_ntac tg $ goal_tree.intro (n, te) $ goal_tree.unres ng,
return e

meta def intro2 (n : name) : ntac expr :=
do t ← henkan target,
   if expr.is_pi t ∨ expr.is_let t then intro2_core n
   else henkan whnf_target >> intro2_core n

meta def intro1 : ntac expr :=
intro2 `_

meta def focus1 {α} (tac : ntac α) : ntac α :=
do g::gs ← henkan get_goals,
   match gs with
   | [] := tac
   | _  := do
      # set_goals [g],
      a ← tac,
      gs' ← # get_goals,
      # set_goals (gs' ++ gs),
      return a
   end

meta def propagate_tags (tac : ntac unit) : ntac unit :=
do tag ← henkan get_main_tag,
   if tag = [] then tac
   else focus1 $ do
     tac,
     gs ← henkan get_goals,
     when (bnot gs.empty) $ do
       new_tag ← henkan get_main_tag,
       when new_tag.empty $ # with_enable_tags (set_main_tag tag)

meta def intro : parse ident_? → ntac unit
| none     := propagate_tags (intro1 >> skip)
| (some h) := propagate_tags (intro2 h >> skip)
meta def rintro (p :parse rintro_parse ) : ntac unit := # interactive.rintro p
meta def ring (red : parse (tk "!")?) (SOP : parse ring.mode) (loc : parse location) : ntac unit := # interactive.ring red SOP loc 
meta def obtain  (p : parse obtain_parse ): ntac unit := # interactive.obtain p
meta def use (l : parse pexpr_list_or_texpr) : ntac unit := # interactive.use l
meta def rcases (p : parse rcases_parse ) : ntac unit := # interactive.rcases p
meta def refine (q : parse texpr) : ntac unit :=
# tactic.refine q

meta def assert (h : name) (t : expr) : ntac expr :=
do tg ← getgoal1,
e ← # tactic.assert h t,
tg1::tg2::_ ← henkan get_goals,
replc_ntac tg $ goal_tree.willhave (goal_tree.unres tg1) (goal_tree.unres tg2), return e
meta def assertv (h : name) (t : expr) (v : expr) : ntac expr :=
do tg ← getgoal1,
e ← # tactic.assertv h t v,
tg1 ← getgoal1,
replc_ntac tg $ goal_tree.have_ e (goal_tree.unres tg1), return e
meta def note (h : name) (t : option expr := none) (pr : expr) : ntac expr :=
do tg ← getgoal1,
e ← # tactic.note h t pr,
tg1 ← getgoal1,
replc_ntac tg $ goal_tree.have_ e (goal_tree.unres tg1), return e
meta def have_aux (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac expr :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← # i_to_expr e,
  v ←henkan $  i_to_expr ``(%%p : %%t),
  assertv h t v
| none, some p := do
  p ←henkan $ i_to_expr p,
  note h none p
| some e, none := henkan (i_to_expr e) >>= assert h
| none, none := do
  u ←henkan $ mk_meta_univ,
  e ← henkan $mk_meta_var (expr.sort u),
  assert h e
end
meta def T : ntac unit :=
do tg ← getgoal1,
replc_ntac tg $ goal_tree.triv (goal_tree.unres tg)
meta def «have» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac unit := 
do e ← have_aux h q₁ q₂,
skip


meta def let_aux (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac expr :=
let h := h.get_or_else `this in
# match q₁, q₂ with
| some e, some p := do
  t ← i_to_expr e,
  v ← i_to_expr ``(%%p : %%t),
  tactic.definev h t v
| none, some p := do
  p ← i_to_expr p,
  tactic.pose h none p
| some e, none := i_to_expr e >>= tactic.define h
| none, none := do
  u ← mk_meta_univ,
  e ← mk_meta_var (expr.sort u),
  tactic.define h e
end
meta def «let» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac unit :=
do tg ← getgoal1,
e ← let_aux h q₁ q₂,
tg2 ← getgoal1,
replc_ntac tg $ goal_tree.willhave (goal_tree.unres e) (goal_tree.unres tg2)

private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

private meta def apply_num_metavars : expr → expr → nat → tactic expr
| f ftype 0     := return f
| f ftype (n+1) := do
  expr.pi m bi d b ← whnf ftype,
  a          ← mk_meta_var d,
  new_f      ← return $ f a,
  new_ftype  ← return $ b.instantiate_var a,
  apply_num_metavars new_f new_ftype n


meta def existsi_org (e : expr) : ntac unit :=
do tg ← getgoal1,
[c]     ← # target' >>= get_constructors_for | fail "existsi tactic failed, target is not an inductive datatype with only one constructor",
   fn      ← # mk_const c,
   fn_type ← # infer_type fn,
   n       ← #  get_arity fn,
   when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments"),
   t       ← # apply_num_metavars fn fn_type (n - 2),
   tact_eapply (expr.app t e),
   t_type  ← # infer_type t >>= whnf,
   e_type  ← # infer_type e,
   (guard t_type.is_pi <|> fail "existsi tactic failed, failed to infer type"),
   (henkan (unify t_type.binding_domain e_type) <|> fail "existsi tactic failed, type mismatch between given term witness and expected type"),
   skip
   --,replc_ntac tg $ goal_tree.existsi e $ goal_tree.unres tg


meta def existsi : parse pexpr_list_or_texpr → ntac unit
| []      := return ()
| (p::ps) := henkan (i_to_expr p) >>= existsi_org >> existsi ps
-- meta def seq'2 (tac1 : ntac unit) (tac2 : ntac unit) : ntac unit :=
-- henkan1 "vovo" $ do g::gs ← get_goals,
--    set_goals [g],
--    henkan2 tac1,
--    all_goals' $ henkan2 tac2,
--    gs' ← get_goals,
--    set_goals (gs' ++ gs)

meta def by_contradiction (n : parse ident?) : ntac unit :=
do tg ← getgoal1,
# tactic.by_contradiction (n.get_or_else `h) $> (),
tg2 ← getgoal1,
replc_ntac tg $ goal_tree.contra (goal_tree.unres tg2)

meta def by_contra (n : parse ident?) : ntac unit :=
by_contradiction n

meta def seq' (tac1 : ntac unit) (tac2 : ntac unit) : ntac unit :=
do g::gs ← henkan get_goals,
   goal_trees_bak ← get_goal_tree,
   # set_goals [g],
   set_goal_tree $ goal_tree.unres g,
   tac1,
   goal_trees ← get_goal_tree,
   goals ← henkan get_goals,
   set_goal_tree $ let l := list.map (λ e, (e,goal_tree.unres e)) goals in goal_tree.andthen goal_trees l,
   all_goals' tac2,
   goal_trees_new ← get_goal_tree,
   gs' ← henkan get_goals,
   # set_goals (gs' ++ gs),
   set_goal_tree $ replc_unres g goal_trees_new goal_trees_bak

meta instance : has_andthen (ntac unit) (ntac unit) (ntac unit) :=
⟨seq'⟩

meta def rotate_left (n: nat): ntac unit:= # tactic.rotate_left n 
end interactive
end ntac

#check tactic.interactive.induction


