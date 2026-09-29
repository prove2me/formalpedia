-- Prove2me | Theorems.Thm_lse_prune_gap_with_margin
-- name    : lse_prune_gap_with_margin
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:33:45.05182+00:00
-- url     : https://prove2.me/theorems/a88a02e9-e11f-46f4-8114-4e51b570b657
-- title:
--   Lse prune gap with margin
-- statement:
--   Formal statement of `lse_prune_gap_with_margin` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem lse_prune_gap_with_margin    {n : ℕ} (τ δ : ℝ) (hτ : 0 < τ) (_hδ : 0 ≤ δ)
--       (x : Fin n → ℝ) (K R : Finset (Fin n)) (hK : K.Nonempty)
--       (hdisj : Disjoint K R) (_hall : K ∪ R = Finset.univ)
--       (hdom : ∀ j ∈ R, x j ≤ Finset.sup' K hK (fun i => x i) - δ) :
--       let lse_all := τ * Real.log (∑ i ∈ (K ∪ R), Real.exp (x i / τ))
--       let lse_keep := τ * Real.log (∑ i ∈ K, Real.exp (x i / τ))
--       lse_all - lse_keep ≤ τ * Real.log (1 + ↑R.card * Real.exp (-δ / τ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/LSEPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/LSEPruning.lean#L177

-- Thm stub generated from Bridges/NeuralCoding/LSEPruning.lean
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

theorem lse_prune_gap_with_margin    {n : ℕ} (τ δ : ℝ) (hτ : 0 < τ) (_hδ : 0 ≤ δ)
    (x : Fin n → ℝ) (K R : Finset (Fin n)) (hK : K.Nonempty)
    (hdisj : Disjoint K R) (_hall : K ∪ R = Finset.univ)
    (hdom : ∀ j ∈ R, x j ≤ Finset.sup' K hK (fun i => x i) - δ) :
    let lse_all := τ * Real.log (∑ i ∈ (K ∪ R), Real.exp (x i / τ))
    let lse_keep := τ * Real.log (∑ i ∈ K, Real.exp (x i / τ))
    lse_all - lse_keep ≤ τ * Real.log (1 + ↑R.card * Real.exp (-δ / τ)) := by sorry
