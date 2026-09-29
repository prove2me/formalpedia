-- Prove2me | solution 1 for FactoringLab.sq_error_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:18:20.302733+00:00
-- url     : https://prove2.me/submissions/21f04433-c295-4a67-b66d-14dc578af685

/-
Proof port from Paul Klemstine's Aether Catalog, commit 53c2925a02:
Catalog/Probability/StructuralOrthogonality.lean, lines 169–199.
The structural-orthogonality dependency is a Proved public theorem.
The missing definitional band-mean helper is reproduced locally.
-/
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_structural_orthogonality

set_option autoImplicit false

open FactoringLab Finset

variable {ι κ : Type*} [DecidableEq κ]

private theorem source_bandMeanFn_comp (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (i : ι) :
    bandMeanFn Ω n Y (n i) = bandMean Ω n Y i := rfl

theorem solution(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
    ∑ i ∈ Ω, (g (n i) - Y i) ^ 2
      = ∑ i ∈ Ω, (g (n i) - bandMean Ω n Y i) ^ 2
        + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 := by
  have hcross := structural_orthogonality Ω n Y (fun k => g k - bandMeanFn Ω n Y k)
  simp only [source_bandMeanFn_comp] at hcross
  have hcross' : ∑ i ∈ Ω, (g (n i) - bandMean Ω n Y i) * (bandMean Ω n Y i - Y i) = 0 := by
    have h2 : ∀ i, (g (n i) - bandMean Ω n Y i) * (bandMean Ω n Y i - Y i)
        = -((g (n i) - bandMean Ω n Y i) * (Y i - bandMean Ω n Y i)) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_neg_distrib, hcross, neg_zero]
  have hexp : ∀ i, (g (n i) - Y i) ^ 2
      = (g (n i) - bandMean Ω n Y i) ^ 2 + (bandMean Ω n Y i - Y i) ^ 2
        + 2 * ((g (n i) - bandMean Ω n Y i) * (bandMean Ω n Y i - Y i)) := by
    intro i; ring
  calc ∑ i ∈ Ω, (g (n i) - Y i) ^ 2
      = ∑ i ∈ Ω, ((g (n i) - bandMean Ω n Y i) ^ 2 + (bandMean Ω n Y i - Y i) ^ 2
          + 2 * ((g (n i) - bandMean Ω n Y i) * (bandMean Ω n Y i - Y i))) :=
        Finset.sum_congr rfl fun i _ => hexp i
    _ = ∑ i ∈ Ω, (g (n i) - bandMean Ω n Y i) ^ 2
          + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcross',
          mul_zero, add_zero]
