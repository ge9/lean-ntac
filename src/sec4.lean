import data.int.basic
import data.real.basic

variables (α : Type*) (p q : α → Prop)
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
(assume as,
and.intro
(assume x,
(as x).left)
(assume x,
(as x).right)
)
(assume as,
have asp : _ , from as.left,
have asq : _ , from as.right,
assume x,
and.intro (asp x) (asq x))
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

----------------------
variable r : Prop
example : α → ((∀ x : α, r) ↔ r) :=
assume al,
iff.intro
(assume ar, ar al) (λ x y , x)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry


variables log exp : real → real
variable log_exp_eq  : ∀ x, log (exp x) = x
variable exp_log_eq  : ∀ {x} , x > 0 → exp (log x) = x
variable exp_pos  : ∀ x, exp x > 0
variable exp_add  : ∀ x y,  exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs

include log_exp_eq exp_log_eq exp_pos exp_add
example (x y z : real) :
exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add,  exp_add]
example (y : real) (h : y > 0): exp (log y) = y :=
exp_log_eq h
theorem log_mul {x y : real} (hx : x>0) (hy:y>0) :
  log (x*y) = log x + log y := 
  sorry

#check sub_self
example (x : ℤ) : x * 0 = 0 :=
sorry
