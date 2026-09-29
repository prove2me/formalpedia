-- Prove2me | solution 1 for lse_prune_gap_with_margin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:20.383979+00:00
-- url     : https://prove2.me/submissions/ab226205-9a3f-4ebe-91f8-ab8114a40b30

-- Sol generated from Bridges/NeuralCoding/LSEPruning.lean
import Mathlib
/-
# Finite-Temperature Pruning Law for Log-Sum-Exp Aggregation

This file formalizes a sharp finite-temperature stability principle for
log-sum-exp (LSE) aggregation under head pruning. The core result:
when coordinates are redundant in the tropical sense (dominated by the
maximum of retained coordinates), finite-temperature smoothing cannot
amplify their removal by more than an entropic term.

## Main results

* `lse_prune_redundant_set_bound` — removing a set of dominated heads
  changes LSE by at most `τ * log (|R| + 1)`.
* `lse_prune_refined_gap_bound` — the refined free-energy defect formula.
* `lse_prune_gap_with_margin` — exponential improvement under uniform gap.

## Cross-domain significance

- **Statistical mechanics**: LSE is free energy; pruning deletes microstates.
- **Information theory**: difference of log-partitions as coding redundancy.
- **Tropical geometry**: certified dequantization estimate (τ → 0 limit).
- **Neural network pruning**: certified head removal under softmax aggregation.

Keywords: certified pruning, attention head redundancy, log-sum-exp stability,
tropicalization error, free energy perturbation, entropy-compression tradeoff,
softmax robustness, idempotent analysis, KL / Gibbs distributions,
low-temperature asymptotics
-/


open Finset Real BigOperators

noncomputable section

/-! ## Helper lemmas about sums of exponentials -/


/-
The sum of exponentials over a set dominates the exponential of the supremum.
This captures the idea that the partition function is at least as large as
the Boltzmann weight of the maximum-energy state.
-/
lemma sum_exp_ge_exp_sup {ι : Type*} (τ : ℝ) (hτ : 0 < τ) (x : ι → ℝ)
    (K : Finset ι) (hK : K.Nonempty) :
    Real.exp (Finset.sup' K hK (fun i => x i) / τ) ≤ ∑ i ∈ K, Real.exp (x i / τ) := by
  -- By definition of supremum, there exists an element $k \in K$ such that $x k = \sup_{i \in K} x i$.
  obtain ⟨k, hk⟩ : ∃ k ∈ K, x k = Finset.sup' K hK (fun i => x i) := by
    exact ( Finset.exists_max_image K x hK ) |> fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k, hk₁, le_antisymm ( Finset.le_sup' ( fun i => x i ) hk₁ ) ( Finset.sup'_le _ _ fun i hi => hk₂ i hi ) ⟩;
  exact Finset.single_le_sum ( fun i _ => Real.exp_nonneg ( x i / τ ) ) hk.1 |> le_trans ( by rw [ ← hk.2 ] )

/-
Monotonicity of exp(·/τ) when τ > 0.
-/

/-
Sum of removed exponentials is bounded by card times the top exponent.
-/

/-
The full sum is at most (|R| + 1) times the kept sum.
-/

/-
Subset monotonicity of sums of exponentials.
-/

/-
Log-transfer: from a ≤ c * b with positivity, deduce τ * log a - τ * log b ≤ τ * log c.
-/

/-
Non-negativity of log ratio when a ≤ b.
-/

/-! ## Main theorems -/

/-
**Redundant set pruning bound.** Removing a set of dominated heads
changes the log-sum-exp by at most `τ * log (|R| + 1)`.

This is the central certified pruning theorem: if every removed head `j ∈ R`
has score dominated by the maximum of the kept set `K`, then the
finite-temperature aggregate changes by a bounded entropic cost.
-/

/-
**Refined free-energy defect bound.** The pruning gap is controlled by
the exact thermodynamic defect formula involving individual excess
Boltzmann weights. This is the strongest form of the pruning bound.
-/

/-
**Margin-refined pruning bound.** When removed heads have a gap δ below
the retained maximum, the pruning cost decays exponentially with δ/τ.
This captures the key insight that deeply dominated heads are virtually
free to prune even at moderate temperature.
-/


theorem solution    {n : ℕ} (τ δ : ℝ) (hτ : 0 < τ) (_hδ : 0 ≤ δ)
    (x : Fin n → ℝ) (K R : Finset (Fin n)) (hK : K.Nonempty)
    (hdisj : Disjoint K R) (_hall : K ∪ R = Finset.univ)
    (hdom : ∀ j ∈ R, x j ≤ Finset.sup' K hK (fun i => x i) - δ) :
    let lse_all := τ * Real.log (∑ i ∈ (K ∪ R), Real.exp (x i / τ))
    let lse_keep := τ * Real.log (∑ i ∈ K, Real.exp (x i / τ))
    lse_all - lse_keep ≤ τ * Real.log (1 + ↑R.card * Real.exp (-δ / τ)) := by
  have h_sum_R_le : ∑ j ∈ R, Real.exp (x j / τ) ≤ R.card * Real.exp ((K.sup' hK (fun i => x i) - δ) / τ) := by
    exact le_trans ( Finset.sum_le_sum fun i hi => Real.exp_le_exp.mpr ( div_le_div_of_nonneg_right ( hdom i hi ) hτ.le ) ) ( by simp +decide [ mul_div_cancel₀ _ hτ.ne' ] );
  have h_sum_K_ge : ∑ i ∈ K, Real.exp (x i / τ) ≥ Real.exp ((K.sup' hK (fun i => x i)) / τ) := by
    exact sum_exp_ge_exp_sup τ hτ x K hK;
  have h_sum_union : ∑ i ∈ K ∪ R, Real.exp (x i / τ) = ∑ i ∈ K, Real.exp (x i / τ) + ∑ j ∈ R, Real.exp (x j / τ) := by
    rw [ Finset.sum_union hdisj ];
  have h_log_union : Real.log (∑ i ∈ K ∪ R, Real.exp (x i / τ)) ≤ Real.log (∑ i ∈ K, Real.exp (x i / τ)) + Real.log (1 + R.card * Real.exp (-δ / τ)) := by
    rw [ h_sum_union, ← Real.log_mul ( ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) hK ) ( ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.exp_nonneg _ ) ];
    refine' Real.log_le_log ( add_pos_of_pos_of_nonneg ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) hK ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) _;
    rw [ show ( ( K.sup' hK fun i => x i ) - δ ) / τ = ( K.sup' hK fun i => x i ) / τ + ( -δ / τ ) by ring, Real.exp_add ] at *;
    nlinarith [ Real.exp_pos ( ( K.sup' hK fun i => x i ) / τ ), Real.exp_pos ( -δ / τ ), mul_le_mul_of_nonneg_right h_sum_K_ge ( Real.exp_nonneg ( -δ / τ ) ) ];
  nlinarith
