-- Prove2me | solution 1 for mme_released_global_empty_cell_matrix_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:44:20.884588+00:00
-- url     : https://prove2.me/submissions/281b6acf-84d0-4c1f-a740-6672dee1a628

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_rank_bridge

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit
universe u
set_option autoImplicit false

/-- A zero coarse count forces every marginal count in that cell to vanish. -/
private theorem empty_cell_center (owner : Fin 6) (c : Cell 8 1 (fun _ _ ↦ 8))
    (hc : ReleasedGlobal.coarseCounts owner c.2 = 0) (i : Fin 3)
    (w : CompleteWord 3) : (ReleasedGlobal.profile owner).2 i c w = 0 := by
  have hd : MoreAsymmetryExactSeed.denominator ^ 4 ≠ 0 := by
    norm_num [MoreAsymmetryExactSeed.denominator]
  have ha : ReleasedGlobal.alpha owner (ReleasedGlobal.shapeEquiv.symm c.2) = 0 :=
    (Nat.mul_eq_zero.mp hc).resolve_right hd
  change (ReleasedGlobal.wordCounts owner i c.2 w : ℝ) /
    (MoreAsymmetryExactSeed.denominator : ℝ) ^ 5 = 0
  have hw : ReleasedGlobal.wordCounts owner i c.2 w = 0 := by
    simp only [ReleasedGlobal.wordCounts, ReleasedGlobal.jointCounts,
      ha, zero_mul, ite_self, Finset.sum_const_zero]
  rw [hw]
  simp

/-- Empty released cells contribute a scalar matrix tensor and logarithmic rate
zero, so they require no separate asymptotic extraction construction. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ)
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
    Restrict (MMObj K 1 1 1) (sixSymmetrization cell) ∧
      Real.exp 0 ≤ (((1 * 1 * 1 : ℕ) : ℝ) ^ tau) := by
  classical
  have hcenter := empty_cell_center owner c hc
  dsimp only
  rw [hc]
  simp only [Nat.mul_zero, if_true, hcenter, abs_zero,
    forall_const, heps, and_true]
  constructor
  · have hfull : Restrict (source K 5 3 0)
        ((source K 5 3 0).basisAllAllowedSubtensor (basis K 5 3 0)
          (fun i x => ∀ r : Fin 0,
            grade (label 5 3 0 (Equiv.refl _) x r) = (c.2.val i).val)) := by
      apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
        (source K 5 3 0) (source K 5 3 0) (basis K 5 3 0) _
        (fun _ => LinearMap.id)
      · simp
      · intro i x hx
        exact (hx (fun r => Fin.elim0 r)).elim
    have hone : Isomorphic (MMObj K 1 1 1)
        (sixSymmetrization (source K 5 3 0)) := by
      rw [← TensorQ.toQ_eq_iff]
      change MMq K 1 1 1 = _
      rw [MMq_one]
      simp only [source, kronPow, sixSymmetrization,
        cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
        ← TensorQ.permAut_toQ, ← TensorQ.toQ_one, map_one, one_mul]
    exact hone.1.trans (mme_sixSymmetrization_restrict hfull)
  · simp


#print axioms solution
