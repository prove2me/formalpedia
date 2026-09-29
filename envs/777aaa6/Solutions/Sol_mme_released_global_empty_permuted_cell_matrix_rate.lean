-- Prove2me | solution 1 for mme_released_global_empty_permuted_cell_matrix_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:03:10.49102+00:00
-- url     : https://prove2.me/submissions/32d5af19-4bef-4008-8761-62029f3687bf

import Theorems.Thm_mme_released_global_empty_cell_matrix_rate
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit
universe u
set_option autoImplicit false

/-- A zero-mass outer cell remains a scalar extraction after any whole-cell
mode permutation, with logarithmic matrix rate zero. -/
theorem solution
    {K : Type u} [Field K] (sigma : Equiv.Perm (Fin 3)) (owner : Fin 6) (k : ℕ)
    (c : Cell 8 1 (fun _ _ ↦ 8))
    (hc : ReleasedGlobal.coarseCounts owner c.2 = 0)
    (eps : ℝ) (heps : 0 ≤ eps) (tau : ℝ) :
    let cell :=
        (source K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner c.2))).basisAllAllowedSubtensor
          (basis K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner c.2))) (fun i x =>
            (∀ r, grade (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner c.2)) (Equiv.refl _) x r) =
              (c.2.val i).val) ∧
            if (k * MME.ReleasedGlobal.coarseCounts owner c.2) = 0 then ∀ a, |(MME.ReleasedGlobal.profile owner).2 i c a| ≤ eps else
            ∀ a, |(count (fun _ : Fin ((k * MME.ReleasedGlobal.coarseCounts owner c.2)) => Unit.unit)
                (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner c.2)) (Equiv.refl _) x) Unit.unit a : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner c.2 : ℕ) : ℝ) -
              ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner c.2 : ℕ) : ℝ)) * (MME.ReleasedGlobal.profile owner).2 i c a| ≤
                ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner c.2 : ℕ) : ℝ)) * eps)
    Restrict (MMObj K 1 1 1) (sixSymmetrization (permObj sigma cell)) ∧
      Real.exp 0 ≤ (((1 * 1 * 1 : ℕ) : ℝ) ^ tau) := by
  obtain ⟨hrestrict, hweight⟩ :=
    mme_released_global_empty_cell_matrix_rate (K := K) owner k c hc eps heps tau
  exact ⟨hrestrict.trans (mme_sixSymmetrization_mode_permutation_iso _ sigma).2,
    hweight⟩


#print axioms solution
