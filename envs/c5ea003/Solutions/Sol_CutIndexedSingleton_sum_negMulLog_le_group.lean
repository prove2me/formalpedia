-- Prove2me | solution 1 for CutIndexedSingleton.sum_negMulLog_le_group
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:31:14.810664+00:00
-- url     : https://prove2.me/submissions/60a38fb3-787e-4548-9b86-fb9dda06111d

-- Sol generated from Novelty/CutIndexedEntropicSingleton.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropicSingleton
import Definitions.Def_Novelty_CutIndexedEntropyMono

/-!
# Cut-indexed defects VI: the entropic cut-wise Singleton inequality

File I proved the *counting* cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S`.  File V showed that the entropy profile
`S ↦ cutEntropy C S` is monotone.  This file completes the entropic mirror of the
`CutData` axioms by proving the missing **chain-rule bound**
`H(T) ≤ H(S) + (|T| - |S|) log q`, and deduces the sharpest form of the theory:

`log |C| ≤ H(S) + (k - |S|) log q` for every cut with `|S| ≤ k = n + 1 - d`.

Because `H(S) ≤ log (cutRank C S)` always, this **implies** the counting cut-wise
Singleton inequality and is strictly stronger whenever the marginal on `S` is not
uniform.

## Main results

* `sum_negMulLog_le_group` : the *log-sum / grouping* inequality
  `∑_{i ∈ F} negMulLog pᵢ ≤ negMulLog (∑ pᵢ) + (∑ pᵢ) log N` for `|F| ≤ N`;
* `card_fiber_restrictCut_le` : a pattern on `S` has at most `q ^ (|T| - |S|)`
  extensions to `T`;
* `cutEntropy_le_add_of_subset` : **the entropic one-block growth bound**
  `H(T) ≤ H(S) + (|T| - |S|) log q`;
* `cutEntropy_eq_log_card_of_resolving` : above the Singleton dimension the cut
  entropy is exactly `log |C|`;
* `entropic_cutwise_singleton` : **the entropic cut-wise Singleton inequality**;
* `entropic_cutwise_singleton_implies_counting` : it implies the counting version
  of file I;
* `entropicDefect_nonneg`, `entropicDefect_eq_zero_iff_isMDS` : the entropic cut
  defect is nonnegative, and at the empty cut it vanishes exactly for MDS codes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): every axiom of `CutData` should have an
entropic mirror, and the mirrored Singleton argument should be *strictly sharper*
than the counting one, because entropy sees the shape of the fibre distribution
and rank only sees its support.

Experiment (Experimenter): the mirror is complete.  The one-block growth bound is
the grouping inequality applied fibre-by-fibre, with `N = q ^ (|T| - |S|)` the
number of extensions of a pattern; the proof of the grouping inequality is the
same `log x ≤ x - 1` estimate that powers
`IITTensorNetwork.sum_negMulLog_le_log_card_support`, but *relativised* to a
sub-block, which is what makes it usable inside a sum over cuts.

Analysis (Analyst): the entropic inequality is strictly stronger: for the code
`{000, 100, 010, 110, 001}` of `Examples.pentaCode` the counting bound at
`S = {0}` is not tight while the entropic one records the exact non-uniformity of
the fibres.  The mirror also explains file III: the quantum inequality is a third
member of the same family, with `log (Schmidt rank)` in place of `H(S)`, and it is
the only one of the three that can *fail* to saturate for MDS codes, because of
purity on the complement.

Critique (Critic): the equality analysis at the empty cut needs `2 ≤ q` (for
`q = 1` all logarithms vanish and the criterion is vacuous) and `C.Nonempty`;
`entropicDefect_eq_zero_iff_isMDS` records both.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}

/-! ## The grouping (log-sum) inequality -/


/-! ## Counting the extensions of a pattern -/


/-! ## The entropic chain-rule bound -/


/-! ## The entropic cut-wise Singleton inequality -/








open CutIndexedSingleton in
theorem solution{ι : Type*} (F : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ F, 0 ≤ p i) {N : ℕ} (hN : F.card ≤ N) (hN0 : 0 < N) :
    ∑ i ∈ F, Real.negMulLog (p i)
      ≤ Real.negMulLog (∑ i ∈ F, p i) + (∑ i ∈ F, p i) * Real.log N := by
  classical
  set A := ∑ i ∈ F, p i with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg hp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  rcases eq_or_lt_of_le hA0 with h | hApos
  · have hzero : ∀ i ∈ F, p i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hp).mp h.symm
    have hl : ∑ i ∈ F, Real.negMulLog (p i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, Real.negMulLog_zero]
    rw [hl, ← h]
    simp
  · have key : ∀ i ∈ F, Real.negMulLog (p i)
        ≤ A / N - p i - p i * Real.log A + p i * Real.log N := by
      intro i hi
      rcases eq_or_lt_of_le (hp i hi) with h0 | h0
      · rw [← h0]
        simp only [Real.negMulLog_zero, zero_mul, sub_zero, add_zero]
        positivity
      · have hx : 0 < A / (N * p i) := by positivity
        have hlog := Real.log_le_sub_one_of_pos hx
        rw [Real.log_div (ne_of_gt hApos) (by positivity),
          Real.log_mul (ne_of_gt hNR) (ne_of_gt h0)] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog h0.le
        have hval : p i * (A / (N * p i) - 1) = A / N - p i := by field_simp
        rw [hval] at hmul
        simp only [Real.negMulLog_def]
        nlinarith [hmul]
    have hsum : ∑ i ∈ F, (A / N - p i - p i * Real.log A + p i * Real.log N)
        = F.card * (A / N) - A - A * Real.log A + A * Real.log N := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.sum_mul, ← hA]
    have hcard : (F.card : ℝ) ≤ N := by exact_mod_cast hN
    have hfrac : (F.card : ℝ) * (A / N) ≤ A := by
      rw [mul_div_assoc'] at *
      rw [div_le_iff₀ hNR]
      nlinarith
    calc ∑ i ∈ F, Real.negMulLog (p i)
        ≤ ∑ i ∈ F, (A / N - p i - p i * Real.log A + p i * Real.log N) :=
          Finset.sum_le_sum key
      _ = F.card * (A / N) - A - A * Real.log A + A * Real.log N := hsum
      _ ≤ Real.negMulLog A + A * Real.log N := by
          simp only [Real.negMulLog_def]
          linarith
