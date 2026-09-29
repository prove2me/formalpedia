-- Prove2me | Definitions.Def_mme_stothers_phi233_outer_grading
-- name    : mme_stothers_phi233_outer_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:02:44.411442+00:00
-- url     : https://prove2.me/theorems/6be764f4-943a-453a-b9f9-6fbd460ca307
-- title:
--   Literal five-grading of the coarse phi_233 constituent
-- statement:
--   The coarse fourth-power constituent $\varphi_{233}$ inherits a five-grading in each tensor mode from the grade of the first square factor. Its canonical basis consists exactly of fourth-power basis coordinates whose two square grades sum to the fixed coarse mode grade $(2,3,3)$. The first-square grade indexes the five internal classes, while the coarse total determines the second-square grade.
--
--   This is the literal internal grading used to interpret the ten $\varphi_{233}$ fine blocks and their tensor-power profile addresses inside the actual coarse constituent.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, and its refinement of the fourth-power constituent T_{233}; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

open MME Module

universe u

namespace MME.StothersFourth.Phi233

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The fixed coarse grade of the three mode spaces of `phi_233`. -/
def modeTotalGrade (s : Fin 3) : Fin 9 :=
  cwFourthBlockType 2 3 3 s

/-- Canonical fourth-power basis coordinates belonging to the coarse `(2,3,3)` constituent in one mode. -/
def ModeIndex (q : ℕ) (s : Fin 3) : Type :=
  {p : (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2)) //
    cwFourthPairGrade q p = modeTotalGrade s}

private theorem mode_span_eq
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Submodule.span K (Set.range (fun p : ModeIndex q s ↦ cwFourthCanonicalBasis K q s p.1)) =
      cwBasisGrade (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) (modeTotalGrade s) := by
  unfold cwBasisGrade
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Canonical basis of one mode of the literal coarse `phi_233` block. -/
noncomputable def canonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (ModeIndex q s) K ((cwFourthConstituent K q 2 3 3).V s) := by
  let b := cwFourthCanonicalBasis K q s
  let v : ModeIndex q s → (cwFourthObj K q).V s := fun p ↦ b p.1
  have hv : LinearIndependent K v := b.linearIndependent.comp _ Subtype.val_injective
  let bs := Basis.span hv
  have heq := mode_span_eq K q s
  let e : Submodule.span K (Set.range v) ≃ₗ[K]
      cwBasisGrade b (cwFourthPairGrade q) (modeTotalGrade s) := LinearEquiv.ofEq _ _ heq
  exact bs.map e

@[simp] theorem canonicalBasis_coe
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (p : ModeIndex q s) :
    (canonicalBasis K q s p).val = cwFourthCanonicalBasis K q s p.1 := by
  unfold canonicalBasis
  rw [Basis.map_apply]
  change ((Basis.span _ p).val : (cwFourthObj K q).V s) = _
  exact Basis.span_apply _ p

/-- The outer fine grade remembers the grade of the first square factor. -/
def outerGrade (q : ℕ) (s : Fin 3) (p : ModeIndex q s) : Fin 5 :=
  cwSquarePairGrade q p.1.1

/-- The literal five-grading of the actual coarse `phi_233` constituent. -/
noncomputable def outerGrading
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthConstituent K q 2 3 3).TypeGrading 5 where
  decomp s := cwBasisGrade (canonicalBasis K q s) (outerGrade q s)
  is_internal s := cwBasisGrade_isInternal (canonicalBasis K q s) (outerGrade q s)

end MME.StothersFourth.Phi233


