-- Prove2me | Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
-- name    : mme_coupled_Ctensor_outer_extraction_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T08:00:02.456207+00:00
-- url     : https://prove2.me/theorems/3f8ebec8-6b20-476a-bb87-05cde474fdaf
-- title:
--   Explicit shared-Z outer extraction maps
-- statement:
--   This module defines the actual modewise outer-extraction maps associated with a primary q=6 hash family and the shared-third-mode star packaging. The X and Y maps keep an outer fiber and one inner index, while the Z map keeps only the outer fiber and uses the common third-mode address. It also records the diagonal choice, mixed address, target inclusion, and finite diagonal-choice set used to prove that all non-diagonal mixed terms vanish.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false

namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]
variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

@[reducible] def outerChoiceType : Fin 3 → Type
  | 0 => Fin A × Fin H
  | 1 => Fin A × Fin H
  | 2 => Fin A

instance outerChoiceFintype (i : Fin 3) :
    Fintype (outerChoiceType (A := A) (H := H) i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

noncomputable instance outerChoiceDecidableEq (i : Fin 3) :
    DecidableEq (outerChoiceType (A := A) (H := H) i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

noncomputable def outerExtractionSummand
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i →
      (T.kronPow (2 * N)).V i →ₗ[K]
        (TensorObj.bigAdd (starObj grading family)).V i
  | 0, p =>
      (gradedBigAddSlot A (starObj grading family) p.1 0).comp
        ((componentInclusion grading family p.1 p.2 0).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family p.1 p.2) 0))
  | 1, p =>
      (gradedBigAddSlot A (starObj grading family) p.1 1).comp
        ((componentInclusion grading family p.1 p.2 1).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family p.1 p.2) 1))
  | 2, a =>
      (gradedBigAddSlot A (starObj grading family) a 2).comp
        (gradedAddressProj grading (2 * N)
          (componentAddress family a (firstFiberIndex family)) 2)

noncomputable def outerExtractionMap
    (family : CWQ6PrimaryHashFamily N L G A H) (i : Fin 3) :
    (T.kronPow (2 * N)).V i →ₗ[K]
      (TensorObj.bigAdd (starObj grading family)).V i :=
  ∑ j, outerExtractionSummand grading family i j

def outerDiagonalChoice
    (a : Fin A) (h : Fin H) :
    ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i
  | 0 => (a, h)
  | 1 => (a, h)
  | 2 => a

def outerChosenAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    Fin 3 → CWQ6CoupledAddress N
  | 0 => componentAddress family (js 0).1 (js 0).2
  | 1 => componentAddress family (js 1).1 (js 1).2
  | 2 => componentAddress family (js 2) (firstFiberIndex family)

def outerMixedAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    CWQ6CoupledAddress N :=
  fun i r => outerChosenAddress family js i i r

noncomputable def outerTargetInclusion
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    ∀ i : Fin 3,
      (gradedAddressBlock grading (outerChosenAddress family js i)).V i →ₗ[K]
        (TensorObj.bigAdd (starObj grading family)).V i
  | 0 => (gradedBigAddSlot A (starObj grading family) (js 0).1 0).comp
      (componentInclusion grading family (js 0).1 (js 0).2 0)
  | 1 => (gradedBigAddSlot A (starObj grading family) (js 1).1 1).comp
      (componentInclusion grading family (js 1).1 (js 1).2 1)
  | 2 => gradedBigAddSlot A (starObj grading family) (js 2) 2

noncomputable def outerDiagonalChoicesCore :
    Finset (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :=
  Finset.univ.image
    (fun p : Fin A × Fin H => outerDiagonalChoice p.1 p.2)

end CoupledCTensorPackaging


