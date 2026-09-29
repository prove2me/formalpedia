-- Prove2me | solution 2 for mme_stothers_phi134_induced_exact_profile_blocks_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T11:10:46.086819+00:00
-- url     : https://prove2.me/submissions/e535d4b0-bee6-42c8-ba6b-9fd89f648f23

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_cyclic_grading_address
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_stothers_phi134_outer_grading_support
import Theorems.Thm_mme_stothers_phi134_exact_cyclic_component_product_restrict_address_block

open MME BigOperators
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

private theorem cyclic_nonzero_supported_core
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → CyclicExactEdge N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading (outerGrading K 6)).blockTensor
        (fun i ↦ cyclicGradingAddress (es i) i j) ≠ 0) :
    CyclicCoordinatewiseSupported (es 0) (es 1) (es 2) := by
  let rhoX : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es s).1.1.1 s
  let rhoY : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es (cyclicPerm s)).2.1.1.1 s
  let rhoZ : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es ((cyclicPerm.trans cyclicPerm) s)).2.2.1.1 s
  have hfactors : ∀ j : Fin (2 * N),
      (outerGrading K 6).blockTensor (fun s ↦ rhoX s j) ≠ 0 ∧
      (outerGrading K 6).blockTensor (fun s ↦ rhoY s j) ≠ 0 ∧
      (outerGrading K 6).blockTensor (fun s ↦ rhoZ s j) ≠ 0 := by
    intro j
    apply mme_cyclic_triple_grading_nonzero_factors
      (outerGrading K 6)
        (fun s ↦ rhoX s j) (fun s ↦ rhoY s j) (fun s ↦ rhoZ s j)
    have hgrade :
        (fun i ↦ cyclicGradingAddress (es i) i j) =
          mmeCyclicTripleGrade
            (fun s ↦ rhoX s j) (fun s ↦ rhoY s j)
              (fun s ↦ rhoZ s j) := by
      funext i
      fin_cases i <;> rfl
    rw [← hgrade]
    exact hblocks j
  refine ⟨?_, ?_, ?_⟩
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoX s j) (hfactors j).1
    refine ⟨r, ?_⟩
    calc
      addressType (mixedAddress (es 0).1.1 (es 1).1.1 (es 2).1.1) j =
          (fun s ↦ rhoX s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoY s j) (hfactors j).2.1
    refine ⟨r, ?_⟩
    calc
      addressType
          (mixedAddress (es 1).2.1.1 (es 2).2.1.1 (es 0).2.1.1) j =
          (fun s ↦ rhoY s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr
  · intro j
    obtain ⟨r, hr⟩ :=
      mme_stothers_phi134_outer_grading_support
        6 (fun s ↦ rhoZ s j) (hfactors j).2.2
    refine ⟨r, ?_⟩
    calc
      addressType
          (mixedAddress (es 2).2.2.1 (es 0).2.2.1 (es 1).2.2.1) j =
          (fun s ↦ rhoZ s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr

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
    have hs := cyclic_nonzero_supported_core
      (K := K) (fun i ↦ (es i).1) (by
        intro j
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
