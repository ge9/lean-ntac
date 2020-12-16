
variable {α : Type*}

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/



theorem append_nil (t: list α) : t ++ list.nil = t := begin simp end


constants (f : nat → nat → nat) (g : nat → nat) (p : nat → nat → Prop)
axioms (fax : ∀ x, f x x = x) (pax : ∀ x, p x x)
local attribute [simp] fax

example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin rsimp; apply pax end

lemma simple (p q : Prop) (h_1 : p) (h_2 : q) : q :=
begin assumption end
universe u
meta def my_tactic (α : Type u) :=
tactic α


namespace my_tactic
namespace interactive
open tactic
meta def find : expr → list expr → tactic
expr
| e []:= failed
| e (h :: hs) :=
  do t ← infer_type h,
   (unify e t >> return h) <|> find e hs
meta def assumption : tactic unit :=
do { ctx ← local_context,
t ← target,
h ← find t ctx,
exact h }
<|> fail "assumption tactic failed"
end interactive
end my_tactic


