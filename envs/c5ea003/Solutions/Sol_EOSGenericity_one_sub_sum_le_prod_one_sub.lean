-- Prove2me | solution 1 for EOSGenericity.one_sub_sum_le_prod_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T23:31:01.299846+00:00
-- url     : https://prove2.me/submissions/ae6fc99d-0b66-495b-99ca-ecd8dcb47aa4

-- Sol generated from NumberTheory/EOSExclusiveDimGenericity.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
/-
# Are the exclusive dimensions really exclusive?  A `q`-Pochhammer genericity bound

Companion to `Catalog/NumberTheory/EOSWidthMonotoneRamp.lean`.

The ramp model draws the boundary token's `k` exclusive directions uniformly at random from a
finite `𝔽_p`-space `V` of dimension `n`.  For the phrase "`k` exclusive dimensions" to be
honest, the `k` draws must actually be linearly independent.  This file quantifies that:

* `EOSGenericity.probIndep_eq_prod` — the probability that `k ≤ n` uniform draws are linearly
  independent is exactly the `q`-Pochhammer product `∏_{i<k} (1 - p^{i-n})`
  (via Mathlib's `card_linearIndependent`);
* `EOSGenericity.one_sub_sum_le_prod_one_sub` — a Weierstrass product inequality, proved by
  induction;
* `EOSGenericity.probIndep_ge` — hence `P(independent) ≥ 1 - (p^k - 1)/((p-1) p^n)`: for
  `k ≪ n` the drawn directions are exclusive with overwhelming probability, so the model of
  the companion file is not vacuous;
* `EOSGenericity.probIndep_antitone_step` — genericity decays with `k`, in the opposite
  direction to the reliability ramp;
* `EOSGenericity.prob_indep_and_cure_ge` — **the synthesis**: with `k` exclusive dimensions the
  probability that the token both occupies a genuine `k`-dimensional subspace *and* escapes all
  `m` obstructions is at least

  `1 - m·p^{-k} - (p^k - 1)/((p-1)·p^n)`,

  a two-sided window: the first term (reliability) shrinks geometrically in `k`, the second
  (genericity) grows geometrically in `k`, so the optimal exclusive width is interior — there is
  a genuine trade-off and no cliff.

### Lab notes

With `p = 2`, `n = 192` (the hidden width of the recurrent cell in the motivating experiment)
and `m = 1`, the bound reads `1 - 2^{-k} - (2^k-1)·2^{-192}`: the genericity loss is utterly
negligible up to `k ≈ 100`, so in the regime of the data (`k ≤ 8`) the reliability term alone
governs, matching the observed monotone ramp `0.25 → 0.33 → 0.83 → 1.00 → 1.00`.
-/


open Module Finset

open EOSGenericity

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]






/-! ## Synthesis: reliability and genericity together -/



open EOSGenericity in
theorem solution(a : ℕ → ℝ) (k : ℕ)
    (h0 : ∀ i ∈ range k, 0 ≤ a i) (h1 : ∀ i ∈ range k, a i ≤ 1) :
    1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h0' : ∀ i ∈ range k, 0 ≤ a i := fun i hi =>
        h0 i (mem_range.mpr (lt_trans (mem_range.mp hi) (Nat.lt_succ_self k)))
      have h1' : ∀ i ∈ range k, a i ≤ 1 := fun i hi =>
        h1 i (mem_range.mpr (lt_trans (mem_range.mp hi) (Nat.lt_succ_self k)))
      have hstep := ih h0' h1'
      have hak0 : 0 ≤ a k := h0 k (mem_range.mpr (Nat.lt_succ_self k))
      have hak1 : a k ≤ 1 := h1 k (mem_range.mpr (Nat.lt_succ_self k))
      have hsum0 : 0 ≤ ∑ i ∈ range k, a i := Finset.sum_nonneg h0'
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have hmul : (1 - ∑ i ∈ range k, a i) * (1 - a k)
          ≤ (∏ i ∈ range k, (1 - a i)) * (1 - a k) :=
        mul_le_mul_of_nonneg_right hstep (by linarith)
      nlinarith [hmul, hsum0, hak0]
