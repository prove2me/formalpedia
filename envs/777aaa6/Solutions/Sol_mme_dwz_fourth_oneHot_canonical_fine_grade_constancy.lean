-- Prove2me | solution 1 for mme_dwz_fourth_oneHot_canonical_fine_grade_constancy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:38:33.061144+00:00
-- url     : https://prove2.me/submissions/9924e9b5-a330-4a9f-a108-19aa0a2f7ac6

import Definitions.Def_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints

open MME MME.DWZFourthTensorLedger MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open Module
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger
open scoped Classical

theorem oneHotLedgerZProfileCounts :
    (componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .atomicExactMM).length = 6 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .squareElementaryBoundary).length = 5 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .square022CyclicTransport).length = 19 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .fourthElementaryBoundary).length = 10 :=
  mme_dwz_fourth_public_component_coverage.1

theorem componentSpecAt_mem_componentMetadata :
    ∀ (i : Fin 180),
    componentSpecAt i ∈ componentMetadata.toList :=
  mme_dwz_fourth_public_component_coverage.2.1

theorem canonicalCyclicLedgerPremisesProp :
    ∀ (metadata : ComponentMetadata) (hmem : metadata ∈ componentMetadata.toList) (htier : publicCoverageTier metadata = PublicCoverageTier.square112ProfileTransport),
    let l := canonicalCyclicL metadata
    let g := canonicalCyclicG metadata
    341 * l < 100 * g ∧
      canonicalCyclicZDenominator metadata = 2 * (l + g) ∧
      CanonicalCyclicProfileShape metadata :=
  mme_dwz_fourth_public_component_coverage.2.2

end MME.DWZFourthTensorLedger
namespace MME.DWZFourthSixFinalSplit
open MME
open MME.DWZFourthScalarLedger
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

theorem properSixEndpoints_of_pointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpointwise : ProperSixEndpointsPointwise tensorAt tau),
    ProperSixEndpoints tensorAt tau :=
  mme_dwz_fourth_six_value_final_node_split.{u}.1

theorem headline :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hproper : ProperSixEndpoints tensorAt tau) (hglobal : FinalSixExtraction tensorAt tau),
    HasSixSymmetricTauValueAtLeast
      (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ) :=
  mme_dwz_fourth_six_value_final_node_split.{u}.2

end MME.DWZFourthSixFinalSplit

namespace MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade

/-- Finite audit for an atomic row. -/
private theorem oneHot_base_active
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true)
    (I J L : Fin 3)
    (haddress : (componentSpecAt i).address = .base I J L) :
    (activeGrade i).val = 0 := by
  decide +kernel +revert

/-- Finite audit for a square row: both the Z total and the ledger's active
cell are the corresponding extreme values. -/
private theorem oneHot_square_total_and_active
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true)
    (I J L : Fin 5)
    (haddress : (componentSpecAt i).address = .square I J L) :
    (L = 0 ∧ (activeGrade i).val = 0) ∨
      (L = 4 ∧ (activeGrade i).val = 2) := by
  decide +kernel +revert

/-- Finite audit for a fourth row: both the Z total and the ledger's active
cell are the corresponding extreme values. -/
private theorem oneHot_fourth_total_and_active
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true)
    (I J L : Fin 9)
    (haddress : (componentSpecAt i).address = .fourth I J L) :
    (L = 0 ∧ (activeGrade i).val = 0) ∨
      (L = 8 ∧ (activeGrade i).val = 4) := by
  decide +kernel +revert

/-- The complete finite audit: every one-hot row selects an extreme
canonical Z total. -/
private theorem oneHot_has_extreme_canonical_Z_total
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    match (componentSpecAt i).address with
    | .base .. => True
    | .square _ _ k => k.val = 0 ∨ k.val = 4
    | .fourth _ _ k => k.val = 0 ∨ k.val = 8 := by
  split
  · trivial
  · rename_i I J L haddress
    rcases oneHot_square_total_and_active i hi I J L haddress with
      ⟨hL, _⟩ | ⟨hL, _⟩
    · left
      simp [hL]
    · right
      simp [hL]
  · rename_i I J L haddress
    rcases oneHot_fourth_total_and_active i hi I J L haddress with
      ⟨hL, _⟩ | ⟨hL, _⟩
    · left
      simp [hL]
    · right
      simp [hL]

/-- A square total-zero fiber has first coordinate grade zero. -/
private theorem q5Square_fine_eq_zero
    (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 0) :
    q5CoordGrade ab.1 = 0 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [q5SquarePairGrade] at hv
  omega

/-- A square total-four fiber has first coordinate grade two. -/
private theorem q5Square_fine_eq_two
    (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 4) :
    q5CoordGrade ab.1 = 2 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [q5SquarePairGrade] at hv
  have hlt0 := (q5CoordGrade ab.1).isLt
  have hlt1 := (q5CoordGrade ab.2).isLt
  omega

/-- A fourth total-zero fiber has first square grade zero. -/
private theorem q5Fourth_fine_eq_zero
    (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7))
    (h : q5FourthPairGrade p = 0) :
    q5SquarePairGrade p.1 = 0 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [q5FourthPairGrade] at hv
  omega

/-- A fourth total-eight fiber has first square grade four. -/
private theorem q5Fourth_fine_eq_four
    (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7))
    (h : q5FourthPairGrade p = 8) :
    q5SquarePairGrade p.1 = 4 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [q5FourthPairGrade] at hv
  have hlt0 := (q5SquarePairGrade p.1).isLt
  have hlt1 := (q5SquarePairGrade p.2).isLt
  omega

/-- The active cell recorded by every one-hot row passes the exact canonical
extreme-fiber criterion. -/
private theorem oneHot_canonicalExtremeActiveMatches
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    canonicalExtremeActiveMatches (componentSpecAt i).address
      (activeGrade i) = true := by
  decide +kernel +revert

/-- Extreme total grade forces every index in the corresponding canonical
fiber to have the indicated fine grade. -/
private theorem canonicalFineZGrade_const_of_extreme
    (address : ComponentAddress) (a : Fin address.zWidth)
    (h : canonicalExtremeActiveMatches address a = true) :
    ∀ x : CanonicalZIndex address, canonicalFineZGrade address x = a := by
  cases address with
  | base I J L =>
      intro x
      apply Fin.ext
      simp [canonicalExtremeActiveMatches] at h
      exact h.symm
  | square I J L =>
      intro x
      apply Fin.ext
      simp [canonicalExtremeActiveMatches] at h
      rcases h with ⟨hL, ha⟩ | ⟨hL, ha⟩
      · have hLF : L = 0 := hL
        rw [ha]
        exact congrArg Fin.val (q5Square_fine_eq_zero x.1 (x.2.trans hLF))
      · have hLF : L = 4 := Fin.ext hL
        rw [ha]
        exact congrArg Fin.val (q5Square_fine_eq_two x.1 (x.2.trans hLF))
  | fourth I J L =>
      intro x
      apply Fin.ext
      simp [canonicalExtremeActiveMatches] at h
      rcases h with ⟨hL, ha⟩ | ⟨hL, ha⟩
      · have hLF : L = 0 := hL
        rw [ha]
        exact congrArg Fin.val (q5Fourth_fine_eq_zero x.1 (x.2.trans hLF))
      · have hLF : L = 8 := Fin.ext hL
        rw [ha]
        exact congrArg Fin.val (q5Fourth_fine_eq_four x.1 (x.2.trans hLF))

/-- On all forty actual ledger rows, the canonical restricted-fiber grading
is constant and equals the unique active profile cell. -/
private theorem headline
    (i : Fin 180)
    (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true) :
    ∀ x : CanonicalZIndex (componentSpecAt i).address,
      canonicalFineZGrade (componentSpecAt i).address x = activeGrade i := by
  exact canonicalFineZGrade_const_of_extreme
    (componentSpecAt i).address (activeGrade i)
    (oneHot_canonicalExtremeActiveMatches i hi)

/-- The raw finite-fiber family form in universe zero. -/
private theorem canonicalFineZGrade_isConstant
    {K : Type 0} [Field K] :
    ConstantOnOneHotRows (K := K)
      (fun i ↦ CanonicalZIndex (componentSpecAt i).address)
      (fun i ↦ canonicalFineZGrade (componentSpecAt i).address) := by
  intro i hi x
  exact headline i hi x

private theorem liftedCanonicalFineZGrade_isConstant
    {K : Type u} [Field K] :
    ConstantOnOneHotRows (K := K)
      (LiftedCanonicalZIndex.{u})
      (liftedCanonicalFineZGrade.{u}) := by
  intro i hi x
  exact headline i hi x.down

/-- Machine-checked cardinality of the family covered by `headline`. -/
private theorem covered_row_count :
    (componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 :=
  oneHotLedgerZProfileCounts.1

end MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade

theorem solution :
    (∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 0),
      q5CoordGrade ab.1 = 0) ∧
    (∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 4),
      q5CoordGrade ab.1 = 2) ∧
    (∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 0),
      q5SquarePairGrade p.1 = 0) ∧
    (∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 8),
      q5SquarePairGrade p.1 = 4) ∧
    (∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
      canonicalExtremeActiveMatches (componentSpecAt i).address
        (activeGrade i) = true) :=
  ⟨q5Square_fine_eq_zero, q5Square_fine_eq_two, q5Fourth_fine_eq_zero, q5Fourth_fine_eq_four, oneHot_canonicalExtremeActiveMatches⟩
