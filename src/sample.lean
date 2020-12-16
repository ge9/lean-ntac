/- declare some constants -/

constant m : nat        -- m is a natural number
constant n : nat
constants b1 b2 : bool  -- declare two constants at once
constant ff : nat → nat
/- check their types -/

#check m            -- output: nat
#check n
#check n + 0        -- nat
#check m * (n + 0)  -- nat
#check b1           -- bool
#check b1 && b2     -- "&&" is boolean and
#check b1 || b2     -- boolean or
#check tt           -- boolean "true"
#print "asfgafg"
def square (x : ℕ) := x * x
def double (x : ℕ) := x + x
def do_twice(f:ℕ → ℕ ) (x:ℕ ): ℕ := f (f x)
#check square
#reduce do_twice double 3
def compose   := λ (α β γ : Type* ) (g: β → γ ) (f : α → β ) (x:α ) ,g (f x)
-- Try some examples of your own.
def nn : Type := ℕ → ℕ 
def Do_Twice (f:nn -> nn) (x:nn):nn := f (f x)
#eval Do_Twice do_twice double 2
def curry (α β γ : Type*) (f: α × β → γ ) : α → β → γ := λ a b, f (a, b) 
def uncurry (α β γ : Type*) (f: α → β → γ ) : (α × β) → γ := λ pair, f pair.1 pair.2
namespace gogo
def tt (x:ℕ ) : ℕ :=
let y := x + x in y * y
#reduce tt 3 -- 36
end gogo
#reduce gogo.tt 3

namespace mylist
constant cons : Π α : Type*, α → list α → list α 
constant cons2 : Π {α : Type*}, α → list α → list α 
constant nil : Π α : Type*, list α
constant nil2 : Π {α : Type*}, list α
-- #check cons 5 nil
#check cons2 5 nil2
end mylist
#check list.nil
#check list.cons
#check @list.nil
#check @list.cons
#check @sigma.mk
#check sigma.mk
variable mklist : ℕ → Type
variable list1 : mklist m
#check sigma.mk m list1
constant Proof : Prop → Type
constant and_commu: Π p q : Prop,
  Proof (implies (and p q) (and p q))
constant and_commu2 (p : Prop)  (q : Prop) :
  Proof (implies (and p q) (and p q))
constant aa : Type
#check and_commu
#check and_commu2
#check ff n
#reduce ff n
section sec3
variables p q : Prop
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
theorem t2 : p → q → p := assume hp : p, assume hq : q, show p, from hp

end sec3

section sec3ex
variables p q r : Prop
-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
iff.intro
(assume hpq:p ∧ q,
show q∧p, from ⟨hpq.right, hpq.left⟩ 
)
(assume hpq:q ∧ p,
show p∧q, from ⟨hpq.right, hpq.left⟩)

example : p ∨ q ↔ q ∨ p := iff.intro
(assume hpq:p ∨ q,
hpq.elim
(assume hp:p, show q∨p , from or.intro_right _ hp)
(assume hq:q, show q∨p , from or.intro_left _ hq)
)

(assume hqp:q ∨ p,
hqp.elim
(assume hq:q, show p∨q , from or.intro_right _ hq)
(assume hp:p, show p∨q , from or.intro_left _ hp)
)
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro
(assume pq_r,
sorry)
(sorry)
-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := 
assume p_notq,
assume p_to_q,
have hq:q, from p_to_q p_notq.left,
show false, from p_notq.right hq
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry

----------


variable s:Prop
theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (classical.em p)
(assume hp : p, hp)
(assume hnp : ¬p, absurd hnp h)
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume p_to_rs,
or.elim (classical.em (p → r))
(or.intro_left (p → s))
(assume notpr:¬(p → r),
suffices ptos:p → s, from or.intro_right (p → r) ptos,
assume hp:p,
suffices nns:¬ ¬ s, from dne nns,
 (assume nots:¬s,
 have rs:r ∨ s, from p_to_rs hp,
 show false, from or.elim rs
 (assume hr:r, 
 have ptor: p → r, from (assume hhp:p, hr),
 show false, from notpr ptor) (assume hs:s, show false, from nots hs)
))

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

theorem ex3:¬ (p ↔ ¬ p) :=
assume pnp,
have l:p → ¬ p, from iff.mp pnp,
have r:¬ p → p, from iff.mpr pnp,
have notp:¬ p, from
(assume hp:p,
show false, from (l hp) hp),
have pp:p, from r notp,
show false, from notp pp
end sec3ex
