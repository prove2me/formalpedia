-- Prove2me | solution 1 for lse_prune_refined_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:10.454038+00:00
-- url     : https://prove2.me/submissions/c032d7a7-1748-4053-8a9c-a2bee5fa77cb

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


theorem solution    {n : ℕ} (τ : ℝ) (hτ : 0 < τ) (x : Fin n → ℝ)
    (K : Finset (Fin n)) (hK : K.Nonempty)
    (R : Finset (Fin n)) (hdisj : Disjoint K R) (hall : K ∪ R = Finset.univ) :
    let s := Finset.sup' K hK (fun i => x i)
    let lse_all := τ * Real.log (∑ i : Fin n, Real.exp (x i / τ))
    let lse_keep := τ * Real.log (∑ i ∈ K, Real.exp (x i / τ))
    lse_all - lse_keep ≤ τ * Real.log (1 + ∑ j ∈ R, Real.exp ((x j - s) / τ)) := by
  simp_all +decide [ ← mul_sub, ← Finset.sum_div _ _ _, mul_div, Real.exp_sub ];
  nontriviality;
  rw [ ← Real.log_mul, ← Real.log_exp ( ∑ i ∈ K, Real.exp ( x i / τ ) ) ];
  · refine' Real.log_le_log _ _;
    · exact Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ Classical.choose hK, Finset.mem_univ _ ⟩;
    · rw [ ← Finset.sum_add_sum_compl ( K ), show ( Kᶜ : Finset ( Fin n ) ) = R from ?_ ];
      · norm_num [ add_mul, sub_div, Real.exp_sub ];
        rw [ Finset.sum_mul _ _ _ ];
        gcongr;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ( Real.exp_pos _ ) ];
        exact mul_le_mul_of_nonneg_left ( by simpa using sum_exp_ge_exp_sup τ hτ x K hK ) ( Real.exp_nonneg _ );
      · rw [ Finset.compl_eq_univ_sdiff, ← hall, Finset.union_sdiff_cancel_left hdisj ];
  · exact ne_of_gt ( add_pos_of_pos_of_nonneg zero_lt_one ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) );
  · exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) hK
