-- Prove2me | solution 1 for mme_dwz_fourth_oneHot_actual_canonical_component_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:46:33.801169+00:00
-- url     : https://prove2.me/submissions/d7589810-b6b9-4606-afe7-a01bd8b3036b

import Definitions.Def_mme_dwz_fourth_oneHot_actual_canonical_component_data_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_integration_splice

open MME MME.DWZFourthPrescribedZ181 MME.DWZFourthPrescribedZ181.OneHotActualCanonical
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open scoped Classical

universe u v

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthPrescribedZ181.OneHotSplice
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open scoped Classical

theorem componentZProfile_eq_normalizedZProfile :
    ∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
    componentZProfile i = normalizedZProfile i :=
  mme_dwz_fourth_oneHot_40_integration_splice.{0}.1

theorem of_properSixEndpointsPointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt i.castSucc)
          ((constantComponentData tensorAt).basis i)
          ((constantComponentData tensorAt).grade i)
          (componentZProfile i) tau
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  mme_dwz_fourth_oneHot_40_integration_splice.{u}.2

end MME.DWZFourthPrescribedZ181.OneHotSplice
namespace MME.DWZFourthTensorLedger.OneHotEndpoints
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped Classical

theorem of_properSixEndpointsPointwise :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (ι : Fin 180 → Type u) (basis : (i : Fin 180) → Basis (ι i) K ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)) (grade : (i : Fin 180) → ι i → Fin (componentSpecAt i).address.zWidth) (tau : ℝ) (hgrade : ConstantOnOneHotRows (K := K) ι grade) (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  mme_dwz_fourth_oneHot_40_prescribedZ_endpoints.{u}

end MME.DWZFourthTensorLedger.OneHotEndpoints
namespace MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open Module
open scoped Classical

theorem q5Square_fine_eq_zero :
    ∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 0),
    q5CoordGrade ab.1 = 0 :=
  mme_dwz_fourth_oneHot_canonical_fine_grade_constancy.1

theorem q5Square_fine_eq_two :
    ∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 4),
    q5CoordGrade ab.1 = 2 :=
  mme_dwz_fourth_oneHot_canonical_fine_grade_constancy.2.1

theorem q5Fourth_fine_eq_zero :
    ∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 0),
    q5SquarePairGrade p.1 = 0 :=
  mme_dwz_fourth_oneHot_canonical_fine_grade_constancy.2.2.1

theorem q5Fourth_fine_eq_four :
    ∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 8),
    q5SquarePairGrade p.1 = 4 :=
  mme_dwz_fourth_oneHot_canonical_fine_grade_constancy.2.2.2.1

theorem oneHot_canonicalExtremeActiveMatches :
    ∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
    canonicalExtremeActiveMatches (componentSpecAt i).address
      (activeGrade i) = true :=
  mme_dwz_fourth_oneHot_canonical_fine_grade_constancy.2.2.2.2

end MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade

namespace MME.DWZFourthPrescribedZ181.OneHotActualCanonical

/-- The globally canonical component grade is constant on all forty one-hot
rows and equals the active ledger cell. -/
private theorem canonicalAddressZGrade_const_of_extreme
    (K : Type u) [Field K] (address : ComponentAddress)
    (a : Fin address.zWidth)
    (h : canonicalExtremeActiveMatches address a = true) :
    ∀ x : CanonicalAddressZIndex K address,
      canonicalAddressZGrade K address x = a := by
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
      · have hzero : cwSquarePairGrade 5 x.down.1 = 0 :=
          x.down.2.trans hL
        have hzero' : q5SquarePairGrade x.down.1 = 0 := by
          simpa [q5CoordGrade, q5SquarePairGrade,
            cwSquareCoordGrade, cwSquarePairGrade] using hzero
        rw [ha]
        change (cwSquareCoordGrade 5 x.down.1.1).val = (0 : Fin 3).val
        exact congrArg Fin.val (q5Square_fine_eq_zero x.down.1 hzero')
      · have hfour : L = 4 := Fin.ext hL
        have htotal : cwSquarePairGrade 5 x.down.1 = 4 :=
          x.down.2.trans hfour
        have htotal' : q5SquarePairGrade x.down.1 = 4 := by
          simpa [q5CoordGrade, q5SquarePairGrade,
            cwSquareCoordGrade, cwSquarePairGrade] using htotal
        rw [ha]
        change (cwSquareCoordGrade 5 x.down.1.1).val = (2 : Fin 3).val
        exact congrArg Fin.val (q5Square_fine_eq_two x.down.1 htotal')
  | fourth I J L =>
      intro x
      apply Fin.ext
      simp [canonicalExtremeActiveMatches] at h
      rcases h with ⟨hL, ha⟩ | ⟨hL, ha⟩
      · have hzero : StothersFourth.cwFourthPairGrade 5 x.down.1 = 0 :=
          x.down.2.trans hL
        have hzero' : q5FourthPairGrade x.down.1 = 0 := by
          simpa [q5CoordGrade, q5SquarePairGrade, q5FourthPairGrade,
            cwSquareCoordGrade, cwSquarePairGrade,
            StothersFourth.cwFourthPairGrade] using hzero
        rw [ha]
        change (cwSquarePairGrade 5 x.down.1.1).val = (0 : Fin 5).val
        exact congrArg Fin.val (q5Fourth_fine_eq_zero x.down.1 hzero')
      · have height : L = 8 := Fin.ext hL
        have htotal : StothersFourth.cwFourthPairGrade 5 x.down.1 = 8 :=
          x.down.2.trans height
        have htotal' : q5FourthPairGrade x.down.1 = 8 := by
          simpa [q5CoordGrade, q5SquarePairGrade, q5FourthPairGrade,
            cwSquareCoordGrade, cwSquarePairGrade,
            StothersFourth.cwFourthPairGrade] using htotal
        rw [ha]
        change (cwSquarePairGrade 5 x.down.1.1).val = (4 : Fin 5).val
        exact congrArg Fin.val (q5Fourth_fine_eq_four x.down.1 htotal')

private theorem componentData_isConstantOnOneHotRows
    (K : Type u) [Field K] :
    ConstantOnOneHotRows (K := K) (componentData K).ι
      (componentData K).grade := by
  intro i hi x
  exact canonicalAddressZGrade_const_of_extreme K
    (componentSpecAt i).address (activeGrade i)
    (oneHot_canonicalExtremeActiveMatches i hi) x

/-- The direct ordinary-to-prescribed lift, now using one coherent canonical
component family rather than a row-local constant choice. -/
private theorem of_properSixEndpointsPointwise
    {K : Type u} [Field K]
    (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise
      (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)) :
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (canonicalQ5Components K) i.castSucc)
          ((componentData K).basis i) ((componentData K).grade i)
          (componentZProfile i) (790643 / 1000000 : ℝ)
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by
  intro i hi
  have h :=
    MME.DWZFourthTensorLedger.OneHotEndpoints.of_properSixEndpointsPointwise
      (tensorAt (canonicalQ5Components K)) (componentData K).ι
      (componentData K).basis (componentData K).grade
      (790643 / 1000000 : ℝ)
      (componentData_isConstantOnOneHotRows K) hordinary i hi
  rw [← OneHotSplice.componentZProfile_eq_normalizedZProfile i hi] at h
  exact h

end MME.DWZFourthPrescribedZ181.OneHotActualCanonical

theorem solution :
    ∀ {K : Type u} [Field K] (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (canonicalQ5Components K) i.castSucc)
          ((componentData K).basis i) ((componentData K).grade i)
          (componentZProfile i) (790643 / 1000000 : ℝ)
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) :=
  of_properSixEndpointsPointwise
