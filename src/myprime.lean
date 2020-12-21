import ntac
import data.nat.prime

open nat

notation n `!`:10000 := nat.factorial n

theorem exists_infinite_primes2 (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
let p := min_fac (n! + 1) in
have f1 : n! + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ factorial_pos _,
have pp : prime p, from min_fac_prime f1,
have np : n ≤ p, from le_of_not_ge $ λ h,
  have h₁ : p ∣ n!, from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  pp.not_dvd_one h₂,
⟨p, np, pp⟩

theorem exists_infinite_primes3 (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
begin[ntac]
let p := min_fac (n! + 1),trace_state,
existsi p,trace_state,
  have f1 : n! + 1 ≠ 1,
  trace_state,
  from (ne_of_gt $ succ_lt_succ $ factorial_pos n),
  trace_state,
  have pp : prime p, from min_fac_prime f1,
split,
{trace_state,
  by_contradiction,trace_state,
  simp at h,trace_state,
  have h1: p ≤ n, from le_of_lt h,
  have h₁ : p ∣ n!, from dvd_factorial (min_fac_pos _) h1,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  from  prime.not_dvd_one pp h₂,
},
T,{assumption}
,trace_state
end