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
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro
  (assume h,
    have hp:p,from h.left,
    have hqr:q ∨ r,from h.right,
    hqr.elim
    (assume hq:q, have (p ∧ q) ,from ⟨hp, hq⟩, or.intro_left  _ this)
    (assume hr:r, have (p ∧ r) ,from ⟨hp, hr⟩, or.intro_right _ this) )
  (assume h, h.elim
    (assume hpq, ⟨hpq.left, or.intro_left  _ hpq.right⟩ )
    (assume hpr, ⟨hpr.left, or.intro_right _ hpr.right⟩ ))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      exact or.inl ⟨h.left, hq⟩,
    exact or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    exact ⟨hpq.left, or.inl hpq.right⟩,
  exact ⟨hpr.left, or.inr hpr.right⟩
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
        { left, split, exact h.left, assumption },
      show (p ∧ q) ∨ (p ∧ r),
        { right, split, exact h.left, assumption },
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
      { cases hpq, split, assumption, left, assumption },
    show p ∧ (q ∨ r),
      { cases hpr, split, assumption, right, assumption }
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry