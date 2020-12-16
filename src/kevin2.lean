
@[reducible] meta def kevin := tactic
namespace kevin
open tactic

meta def copy_decl (d : declaration) : tactic unit :=
add_decl $ d.update_name $ d.to_name.update_prefix `kevin.interactive

@[reducible] meta def filter (d : declaration) : bool :=
d.to_name ∉ [`tactic.interactive.induction, `tactic.interactive.ap]

meta def copy_decls : tactic unit :=
do env ← get_env,
  let ls := env.fold [] list.cons,
  ls.mmap' $ λ dec, when (dec.to_name.get_prefix = `tactic.interactive ∧ filter dec) (copy_decl dec)




--meta instance : monad kevin := by delta kevin; apply_instance

--meta instance : alternative kevin := by delta kevin; apply_instance

meta def step {α} (c : kevin α) : kevin unit := 
c >> return ()
meta def istep {α} (line0 col0 : ℕ) (line col : ℕ) (t : tactic α) : kevin unit :=
λ s, (@scope_trace _ line col (λ _, step t s)).clamp_pos line0 line col
meta def save_info := tactic.save_info

meta def execute (c : kevin unit) : kevin unit := 
c

--meta def trace_state {α : Type}

end kevin

#check tactic.interactive.induction

meta def kevin.interactive.induction :
  interactive.parse tactic.interactive.cases_arg_p →
  interactive.parse interactive.types.using_ident →
  interactive.parse interactive.types.with_ident_list →
  interactive.parse (optional (lean.parser.tk "generalizing" *> lean.parser.many lean.parser.ident)) → tactic unit
:= tactic.interactive.induction

run_cmd kevin.copy_decls

example (n : ℕ) : true :=
begin 
  [kevin]
  induction n,
    sorry, sorry
end

example (n : ℕ) : true :=
begin
  induction n,
    sorry, sorry
end

lemma simple2 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
begin[kevin] trace_state,assumption,trace_state end

lemma simple22 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
by kevin.interactive.assumption

lemma simple3 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
begin assumption end

constants (f : nat → nat → nat) (g : nat → nat) (p : nat → nat → Prop)
axioms (fax : ∀ x, f x x = x) (pax : ∀ x, p x x)
local attribute [simp] fax

example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin[kevin] rsimp; apply pax end
example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin  rsimp; apply pax end

meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."

meta def my_second_tactic' : tactic unit :=
do
  tactic.trace  $ "Hello," ++ "df",
  tactic.trace "World."

example : true :=
begin
  my_first_tactic,
  my_second_tactic',
  trivial
end