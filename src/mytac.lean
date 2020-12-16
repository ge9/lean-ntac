import ntac

theorem append_nil (t: list nat) : t ++ list.nil = t := begin[smt] trace_state, simp, trace_state end
-- theorem append_nil2 (t: list nat) : t ++ list.nil = t := by smt_tactic.interactive.simp

-- set_option pp.beta false

example (n : ℕ) : true :=
begin 
  [ntac]
  trace_state,
  trace_state,
  trace_state,
  induction n,
  trace_state,
  trace_state,
  trace_state,
    sorry, sorry
end
example (n : ℕ) : true :=
begin 
  [ntac]
  induction n,
    sorry, sorry
end

example (n : ℕ) : true :=
begin
  trace_state,
  induction n,
  trace_state,
    sorry, sorry
end


lemma simple2 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
by ntac.henkan2 ntac.interactive.assumption


lemma simple5 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
begin[ntac] trace_state, assumption, trace_state end

lemma simple3 (p q : Prop) (h_1 : p) (h_2 : q) : q :=
begin assumption end

constants (f : nat → nat → nat) (g : nat → nat) (p : nat → nat → Prop)
axioms (fax : ∀ x, f x x = x) (pax : ∀ x, p x x)
local attribute [simp] fax

example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin[ntac] rsimp, apply pax, trace_state end


example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] trace_state, skiptgt, trace_state, split; assumption, trace_state end
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin trace_state, trace_state, split; assumption, trace_state end
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] trace_state, skiptgt, split;{trace_state, assumption,trace_state},trace_state end


example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] split,trace_state, assumption,trace_state,assumption,trace_state end
example (p q : Prop) (hc : p) (hqw : q) : p ∧ q :=
begin[ntac] split,trace_state,rotate_left 1, trace_state,assumption,trace_state,assumption,trace_state end



example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin[ntac] trace_state, rsimp, trace_state, apply pax, trace_state end

example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin   rsimp; trace_state, apply pax end

example (a b c : nat) (h_1 : a = g b) (h_2 : a = b) : p (f (g a) a) b :=
begin   rsimp; apply pax end
def c := tt
def d := tt

