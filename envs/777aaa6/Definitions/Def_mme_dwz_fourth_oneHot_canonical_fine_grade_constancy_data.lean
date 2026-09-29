-- Prove2me | Definitions.Def_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy_data
-- name    : mme_dwz_fourth_oneHot_canonical_fine_grade_constancy_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:37:42.370917+00:00
-- url     : https://prove2.me/theorems/93bd6a3e-e1cb-4345-8185-e4804305c4c5
-- title:
--   Constancy of the canonical fine grade on one-hot ledger rows
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_oneHot_canonical_fine_grade_constancy, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Mathlib.Tactic
import Definitions.Def_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints

open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open Module
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade

/-! ## Exact restricted-fiber basis constructor -/
/-- Source-level definition used by the public `cwBasisGrade`: span the
basis vectors in one grade fiber.  It is reproduced locally because the
compact workspace exposes `cwBasisGrade` only through a signature mirror. -/
def basisGradeSpan {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) {t : ℕ} (grade : ι → Fin t) (a : Fin t) :
    Submodule K V :=
  Submodule.span K (b '' {i | grade i = a})

/-- Index set of the canonical basis restricted to one grade class. -/
def BasisGradeFiber {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (a : Fin t) : Type u :=
  {i : ι // grade i = a}

private theorem basisGradeFiber_span_eq
    {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) {t : ℕ} (grade : ι → Fin t) (a : Fin t) :
    Submodule.span K
        (Set.range (fun p : BasisGradeFiber grade a ↦ b p.1)) =
      basisGradeSpan b grade a := by
  unfold basisGradeSpan
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- The canonical grade fiber really carries a basis indexed by the subtype
used below.  This is the same `Basis.span` construction used in public
restricted-canonical-basis definitions. -/
noncomputable def basisGradeFiberBasis
    {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) {t : ℕ} (grade : ι → Fin t) (a : Fin t) :
    Basis (BasisGradeFiber grade a) K (basisGradeSpan b grade a) := by
  let v : BasisGradeFiber grade a → V := fun p ↦ b p.1
  have hv : LinearIndependent K v :=
    b.linearIndependent.comp (fun p : BasisGradeFiber grade a ↦ p.1)
      Subtype.val_injective
  let bs := Basis.span hv
  have heq := basisGradeFiber_span_eq b grade a
  let e : Submodule.span K (Set.range v) ≃ₗ[K] basisGradeSpan b grade a :=
    LinearEquiv.ofEq _ _ heq
  exact bs.map e

/-- The `q = 5` specialization of public `cwSquareCoordGrade`. -/
def q5CoordGrade (a : Fin 7) : Fin 3 :=
  if a.val = 0 then 0 else if a.val = 6 then 2 else 1

/-- The `q = 5` specialization of public `cwSquarePairGrade`. -/
def q5SquarePairGrade (ab : Fin 7 × Fin 7) : Fin 5 :=
  ⟨(q5CoordGrade ab.1).val + (q5CoordGrade ab.2).val, by
    have h0 := (q5CoordGrade ab.1).isLt
    have h1 := (q5CoordGrade ab.2).isLt
    omega⟩

/-- The `q = 5` specialization of public
`StothersFourth.cwFourthPairGrade`. -/
def q5FourthPairGrade
    (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) : Fin 9 :=
  ⟨(q5SquarePairGrade p.1).val + (q5SquarePairGrade p.2).val, by
    have h0 := (q5SquarePairGrade p.1).isLt
    have h1 := (q5SquarePairGrade p.2).isLt
    omega⟩

/-- Canonical basis indices in the Z-mode class selected by a ledger
address.  These are exactly the grade fibers used to make bases of the
`cwBasisGrade` submodules in the public canonical grading definitions. -/
def CanonicalZIndex : ComponentAddress → Type
  | .base _ _ k => {a : Fin 7 // q5CoordGrade a = k}
  | .square _ _ k => {ab : Fin 7 × Fin 7 // q5SquarePairGrade ab = k}
  | .fourth _ _ k =>
      {p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
        q5FourthPairGrade p = k}

/-- The natural first-factor fine grade on square/fourth canonical fibers.
Atomic blocks use the one-cell sentinel normalization. -/
def canonicalFineZGrade (address : ComponentAddress) :
    CanonicalZIndex address → Fin address.zWidth := by
  cases address with
  | base I J L =>
      exact fun _ => (0 : Fin 2)
  | square I J L =>
      exact fun ab => q5CoordGrade ab.1.1
  | fourth I J L =>
      exact fun p => q5SquarePairGrade p.1.1

/-- Boolean interface saying that a proposed active cell is the correct
extreme first-factor grade for a canonical Z fiber. -/
def canonicalExtremeActiveMatches (address : ComponentAddress)
    (a : Fin address.zWidth) : Bool :=
  match address with
  | .base .. => a.val == 0
  | .square _ _ L =>
      (L.val == 0 && a.val == 0) || (L.val == 4 && a.val == 2)
  | .fourth _ _ L =>
      (L.val == 0 && a.val == 0) || (L.val == 8 && a.val == 4)

/-- Universe-lifted canonical fiber indices for an arbitrary-universe
coefficient field.  `ComponentBasisGradeData` uses the field universe for its
index family, so this harmless lift is the form used by a fully general
attachment. -/
def LiftedCanonicalZIndex (i : Fin 180) : Type u :=
  ULift.{u} (CanonicalZIndex (componentSpecAt i).address)

def liftedCanonicalFineZGrade (i : Fin 180) :
    LiftedCanonicalZIndex.{u} i →
      Fin (componentSpecAt i).address.zWidth :=
  fun x ↦ canonicalFineZGrade (componentSpecAt i).address x.down

end MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade


