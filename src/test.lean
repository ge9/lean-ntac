lemma zero_max (m : ℕ) : max 0 m = m :=
max_eq_right (nat.zero_le m)