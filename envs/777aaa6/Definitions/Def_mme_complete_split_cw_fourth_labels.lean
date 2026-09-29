-- Prove2me | Definitions.Def_mme_complete_split_cw_fourth_labels
-- name    : mme_complete_split_cw_fourth_labels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T21:25:11.634941+00:00
-- url     : https://prove2.me/theorems/df18701e-7b68-4b39-958d-cba6ff29f84c
-- title:
--   Canonical complete-split labels of actual CW fourth constituents
-- statement:
--   Use the existing literal ((CW_q tensor CW_q) tensor (CW_q tensor CW_q)) and its canonical coarse grading. A coordinate ((a,b),(c,d)) receives its four literal level-one grades, in that order. For each constituent (I,J,L), its actual mode subspace receives the subset of the canonical fourth basis with the specified coarse grade. ULift changes the index universe only. These concrete bases and full-word labels instantiate the all-three-mode approximate complete-split projection on the Nth power of the actual constituent. There are no arbitrary basis-label hypotheses, positivity/nonemptiness assumptions, asymptotic value assumptions, or numerical claims.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, printed pp.14-15, Definitions 3.4-3.6. Literal level-three full-word labels on the existing fourth-power CW tensor; q=5 is the More Asymmetry consumer.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.LinearAlgebra.Basis.Submodule

/-!
Canonical full fine-word labels and complete-profile projections of actual
fourth-power CW constituents. This specializes More Asymmetry v2,
Definitions 3.4--3.6, to level three using the existing literal tensor.
No arbitrary basis-label fields or tensor-value hypotheses are introduced.
-/

set_option autoImplicit false
set_option warningAsError true

universe u

open MME Module BigOperators MME.StothersFourth
open scoped NNReal

namespace MME.CompleteSplit.CWFourth

abbrev Coordinate (q : ℕ) :=
  (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2))

/-- The two literal level-one CW grades in a canonical square coordinate. -/
def squareWord (q : ℕ) (p : Fin (q + 2) × Fin (q + 2)) : CompleteWord 2 :=
  ![cwSquareCoordGrade q p.1, cwSquareCoordGrade q p.2]

/-- Full fine-word order follows the actual parenthesization ((a,b),(c,d)). -/
def fullWord (q : ℕ) (p : Coordinate q) : CompleteWord 3 :=
  ![cwSquareCoordGrade q p.1.1, cwSquareCoordGrade q p.1.2,
    cwSquareCoordGrade q p.2.1, cwSquareCoordGrade q p.2.2]

/-- Actual canonical fourth coordinates belonging to a fixed coarse class. -/
def CoarseCoordinate (q : ℕ) (c : Fin 9) :=
  {p : Coordinate q // cwFourthPairGrade q p = c}

instance (q : ℕ) (c : Fin 9) : Fintype (CoarseCoordinate q c) := by
  unfold CoarseCoordinate
  infer_instance

instance (q : ℕ) (c : Fin 9) : DecidableEq (CoarseCoordinate q c) := by
  unfold CoarseCoordinate
  infer_instance

private noncomputable def coarseVectors
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 9) :
    CoarseCoordinate q c → (cwFourthObj K q).V i :=
  fun p ↦ cwFourthCanonicalBasis K q i p.1

private theorem coarseVectors_independent
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 9) :
    LinearIndependent K (coarseVectors K q i c) :=
  (cwFourthCanonicalBasis K q i).linearIndependent.comp _ Subtype.val_injective

private theorem coarseVectors_span
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 9) :
    Submodule.span K (Set.range (coarseVectors K q i c)) =
      (cwFourthCanonicalGrading K q).classOf i c := by
  change Submodule.span K (Set.range (coarseVectors K q i c)) =
    cwBasisGrade (cwFourthCanonicalBasis K q i) (cwFourthPairGrade q) c
  unfold cwBasisGrade
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Canonical subset basis of a mode's actual fourth coarse-grading class. -/
noncomputable def coarseClassBasis
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 9) :
    Basis (CoarseCoordinate q c) K ((cwFourthCanonicalGrading K q).classOf i c) :=
  (Basis.span (coarseVectors_independent K q i c)).map
    (LinearEquiv.ofEq _ _ (coarseVectors_span K q i c))

/-- The lift changes only the index universe, not the canonical coordinate. -/
def LiftedCoarseCoordinate (q : ℕ) (c : Fin 9) : Type u :=
  ULift.{u} (CoarseCoordinate q c)

instance (q : ℕ) (c : Fin 9) : Fintype (LiftedCoarseCoordinate.{u} q c) := by
  unfold LiftedCoarseCoordinate
  infer_instance

instance (q : ℕ) (c : Fin 9) : DecidableEq (LiftedCoarseCoordinate.{u} q c) := by
  unfold LiftedCoarseCoordinate
  infer_instance

/-- Canonical basis in every mode of the existing literal (I,J,L) constituent. -/
noncomputable def constituentBasis
    (K : Type u) [Field K] (q : ℕ) (I J L : Fin 9) (i : Fin 3) :
    Basis (LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) K
      ((cwFourthConstituent K q I J L).V i) :=
  (coarseClassBasis K q i (cwFourthBlockType I J L i)).reindex Equiv.ulift.symm

/-- Full canonical fine word carried by one actual constituent basis index. -/
def constituentLabel (q : ℕ) (I J L : Fin 9) (i : Fin 3)
    (p : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) : CompleteWord 3 :=
  fullWord q p.down.1

/-- Source Definition 3.6 on an actual fourth-power CW constituent.
The basis and fine-word labels are the concrete canonical ones above. -/
noncomputable def restrictedConstituentPower
    (K : Type u) [Field K] (q : ℕ) (I J L : Fin 9)
    (beta : Fin 3 → Profile 3) (epsilon : ℝ≥0) (N : ℕ) : TensorObj K 3 :=
  restrictedPower (cwFourthConstituent K q I J L)
    (constituentBasis K q I J L) (constituentLabel q I J L) beta epsilon N

end MME.CompleteSplit.CWFourth


