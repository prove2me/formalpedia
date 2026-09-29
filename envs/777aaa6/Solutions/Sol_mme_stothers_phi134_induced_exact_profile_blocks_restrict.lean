-- Prove2me | solution 1 for mme_stothers_phi134_induced_exact_profile_blocks_restrict
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:46:42.880952+00:00
-- url     : https://prove2.me/submissions/e8618fc1-13ec-4f38-8504-7902c7b87895
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_cyclic_grading_address
import Definitions.Def_mme_stothers_phi134_outer_grading
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_stothers_phi134_cyclic_nonzero_block_implies_supported_mix
import Theorems.Thm_mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block

open MME BigOperators
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (kept : Finset (CyclicExactEdge N alpha beta gamma delta))
    (hdiag : ∀ x y z : kept,
      CyclicCoordinatewiseSupported x.1 y.1 z.1 → x = y ∧ y = z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization
          (TensorObj.kronFin 8 (fun r ↦
            (componentObj K 6 r).kronPow
              (profileMultiplicity alpha beta gamma delta r)))))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)).kronPow
          (2 * N)) := by
  classical
  let A := fun j : Fin kept.card ↦
    cyclicGradingAddress (kept.equivFin.symm j).1
  have hind (js : Fin 3 → Fin kept.card)
      (hnz : ∀ r,
        (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
          (fun i ↦ A (js i) i r) ≠ 0) :
      ∃ j, js = fun _ ↦ j := by
    let es := fun i ↦ kept.equivFin.symm (js i)
    have hs := mme_stothers_phi134_cyclic_nonzero_block_implies_supported_mix
      (K := K) (es 0).1 (es 1).1 (es 2).1 (by
        intro j
        have he :
            (![(es 0).1, (es 1).1, (es 2).1] :
                Fin 3 → CyclicExactEdge N alpha beta gamma delta) =
              fun i ↦ (es i).1 := by
          funext i
          fin_cases i <;> rfl
        rw [he]
        exact hnz j)
    obtain ⟨h01, h12⟩ := hdiag (es 0) (es 1) (es 2) hs
    have hj01 : js 0 = js 1 := kept.equivFin.symm.injective h01
    have hj12 : js 1 = js 2 := kept.equivFin.symm.injective h12
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i <;> simp_all
  have hh := mme_induced_graded_address_blocks_restrict
    (mmeCyclicTripleGrading (outerGrading K 6)) A hind
  refine TensorObj.Restrict.trans (mme_bigAdd_mono_restrict ?_) hh
  intro j
  exact
    mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block
      6 (kept.equivFin.symm j).1
