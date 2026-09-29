-- Prove2me | solution 1 for RSumWitnessBarrier.exists_rsum_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:33.945216+00:00
-- url     : https://prove2.me/submissions/c88ad355-2da0-4d53-bc0b-07ca7f6d7712

-- Sol generated from Applications/RSumWitnessBarrier.lean
import Mathlib
import Definitions.Def_Applications_RSumWitnessBarrier
/-
# The `r`-SUM witness barrier: arity never compresses the search box

Fourth cycle.  `Catalog/Applications/ThreeSumSearchSpace.lean` proved, for arity
`3`, that a witness with positive entries bounded by `K` exists **iff** `p ≤ 3K`.
The obvious hypothesis — raised as a conjecture at the end of cycle 3 — is that
the same dichotomy holds at every arity `r`, with threshold `p ≤ r·K`.  Here it
is proved.

* `no_rsum_witness_of_small` : if `r·K < p` no `r`-tuple in the box `[1,K]^r`
  has sum divisible by `p`;
* `exists_rsum_witness` : if `r ≤ p ≤ r·K` (and `r ≥ 1`) such a tuple exists,
  by an explicit greedy construction (induction on `r` using `Fin.cons`);
* `rsum_witness_iff` : the exact dichotomy;
* `rsum_entry_size_barrier` : consequently, for a balanced semiprime `N = p*q`
  with `q ≤ 2p`, any arity-`r` search box that contains a witness obeys
  `N ≤ 2·r²·K²`, i.e. `K ≥ √N / (r√2)`.

Interpretation: increasing the arity shrinks the required entry magnitude only
by the *linear* factor `r`, never polynomially.  Combined with
`BirthdayBoundHierarchy.birthday_barrier_sqrt` (the number of inspected
selections must exceed `p` at every arity) both axes of the hierarchy are now
pinned: neither the count nor the magnitude improves past `√N`.
-/

open RSumWitnessBarrier

open Finset








open RSumWitnessBarrier in
theorem solution: ∀ {p K r : ℕ}, 1 ≤ r → r ≤ p → p ≤ r * K →
    ∃ x : Fin r → ℕ, InBox K x ∧ ∑ i, x i = p := by
  intro p K r
  induction r generalizing p with
  | zero => intro hr; omega
  | succ n ih =>
    intro _ hlb hub
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hub' : p ≤ K := by simpa using hub
      refine ⟨fun _ => p, fun i => ?_, by simp⟩
      show 0 < p ∧ p ≤ K
      exact ⟨by omega, hub'⟩
    · -- peel off one coordinate, greedily as large as possible
      have hK : 1 ≤ K := by nlinarith
      set c := min K (p - n) with hc
      have hc1 : 1 ≤ c := by omega
      have hcK : c ≤ K := by omega
      have hrem_lb : n ≤ p - c := by omega
      have hrem_ub : p - c ≤ n * K := by
        rcases le_or_gt K (p - n) with h | h
        · have : c = K := by omega
          have : p ≤ n * K + K := by
            have : (n + 1) * K = n * K + K := by ring
            omega
          omega
        · have : c = p - n := by omega
          have : p - c = n := by omega
          nlinarith
      obtain ⟨y, hy, hsum⟩ := ih hn hrem_lb hrem_ub
      refine ⟨Fin.cons c y, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ⟨hc1, hcK⟩
        · intro j; simpa using hy j
      · rw [Fin.sum_cons, hsum]
        omega
