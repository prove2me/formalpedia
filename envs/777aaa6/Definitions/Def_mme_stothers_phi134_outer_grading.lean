-- Prove2me | Definitions.Def_mme_stothers_phi134_outer_grading
-- name    : mme_stothers_phi134_outer_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T10:23:21.652811+00:00
-- url     : https://prove2.me/theorems/49b43156-21e2-424c-8683-9c2dfe0ce745
-- title:
--   Literal outer five-grading of the phi_134 fourth-power constituent
-- statement:
--   For the literal fourth-power Coppersmith--Winograd constituent of coarse type $(1,3,4)$, define the canonical basis of each mode by restricting the fourth-power tensor basis to that coarse grade, and grade it further by the first square factor's grade. This is the five-class outer grading used to realize the eight fine components of $\Phi_{1,3,4}$ inside the actual coarse constituent. It supplies the source tensor required by induced address-block zeroing.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), pp. 364--365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

open MME Module

universe u

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def modeTotalGrade (s : Fin 3) : Fin 9 := cwFourthBlockType 1 3 4 s

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

noncomputable def canonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (ModeIndex q s) K ((cwFourthConstituent K q 1 3 4).V s) := by
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

def outerGrade (q : ℕ) (s : Fin 3) (p : ModeIndex q s) : Fin 5 :=
  cwSquarePairGrade q p.1.1

noncomputable def outerGrading
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthConstituent K q 1 3 4).TypeGrading 5 where
  decomp s := cwBasisGrade (canonicalBasis K q s) (outerGrade q s)
  is_internal s := cwBasisGrade_isInternal (canonicalBasis K q s) (outerGrade q s)

end MME.StothersFourth.Phi134


