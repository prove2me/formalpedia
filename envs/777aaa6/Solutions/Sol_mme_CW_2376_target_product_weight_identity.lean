-- Prove2me | solution 1 for mme_CW_2376_target_product_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:33:45.102966+00:00
-- url     : https://prove2.me/submissions/478df474-91c0-45bd-965a-01227e9b671c

import Definitions.Def_mme_CW_2376_profile_dominance_weights

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

@[simp] private theorem cwSquareBlockType_eq_iff
    (I J K I' J' K' : Fin 5) :
    cwSquareBlockType I J K = cwSquareBlockType I' J' K' ↔
      I = I' ∧ J = J' ∧ K = K' := by
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    simpa [cwSquareBlockType] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem prod_fin3 (f : Fin 3 → ℕ) :
    ∏ i, f i = f 0 * f 1 * f 2 := by
  change Finset.prod (Finset.univ : Finset (Fin 3)) f = _
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  simp [mul_assoc]

/-- The four target orbit weights are one exact integral product-form family. -/
theorem solution
    (m : ℕ) (sigma : Fin 3 → Fin 5)
    (hsigma : sigma ∈ cw2376TargetJointTypes) :
    cw2376DominanceScale * cw2376ProfileMultiplicity m sigma =
      m * ∏ i : Fin 3, cw2376DominanceGradeWeight (sigma i) := by
  simp only [cw2376TargetJointTypes, Finset.mem_union] at hsigma
  rcases hsigma with ((hsigma | hsigma) | hsigma) | hsigma
  · simp only [cw2376ScalarTypes, Finset.mem_insert,
      Finset.mem_singleton] at hsigma
    rcases hsigma with rfl | rfl | rfl <;>
      rw [prod_fin3] <;>
      norm_num [cw2376DominanceScale, cw2376DominanceGradeWeight,
        cw2376ProfileMultiplicity, cw2376ScalarTypes, cw2376RectTypes,
        cw2376CentralTypes, cw2376CoupledTypes, cwSquareBlockType,
        Fin.sum_univ_succ, Fin.ext_iff] <;> ring
  · simp only [cw2376RectTypes, Finset.mem_insert,
      Finset.mem_singleton] at hsigma
    rcases hsigma with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [prod_fin3] <;>
      norm_num [cw2376DominanceScale, cw2376DominanceGradeWeight,
        cw2376ProfileMultiplicity, cw2376ScalarTypes, cw2376RectTypes,
        cw2376CentralTypes, cw2376CoupledTypes, cwSquareBlockType,
        Fin.sum_univ_succ, Fin.ext_iff] <;> ring
  · simp only [cw2376CentralTypes, Finset.mem_insert,
      Finset.mem_singleton] at hsigma
    rcases hsigma with rfl | rfl | rfl <;>
      rw [prod_fin3] <;>
      norm_num [cw2376DominanceScale, cw2376DominanceGradeWeight,
        cw2376ProfileMultiplicity, cw2376ScalarTypes, cw2376RectTypes,
        cw2376CentralTypes, cw2376CoupledTypes, cwSquareBlockType,
        Fin.sum_univ_succ, Fin.ext_iff] <;> ring
  · simp only [cw2376CoupledTypes, Finset.mem_insert,
      Finset.mem_singleton] at hsigma
    rcases hsigma with rfl | rfl | rfl <;>
      rw [prod_fin3] <;>
      norm_num [cw2376DominanceScale, cw2376DominanceGradeWeight,
        cw2376ProfileMultiplicity, cw2376ScalarTypes, cw2376RectTypes,
        cw2376CentralTypes, cw2376CoupledTypes, cwSquareBlockType,
        Fin.sum_univ_succ, Fin.ext_iff] <;> ring
