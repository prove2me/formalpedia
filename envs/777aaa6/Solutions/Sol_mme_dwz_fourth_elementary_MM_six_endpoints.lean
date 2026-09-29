-- Prove2me | solution 1 for mme_dwz_fourth_elementary_MM_six_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:31:41.049631+00:00
-- url     : https://prove2.me/submissions/bd761ed6-b90d-4ac6-91bf-c873d4a4b4cf

import Definitions.Def_mme_dwz_fourth_elementary_MM_six_endpoints_data
import Theorems.Thm_mme_dwz_fourth_public_ordinary_181_reduction
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_stothers_elementary_fourth_constituent_MM_restrict
import Theorems.Thm_mme_stothers_cwFourth_cyclic_block_iso
import Theorems.Thm_mme_stothers_cwFourth_swapped_block_iso
import Theorems.Thm_mme_CW_block_is_MM_at_110
import Theorems.Thm_mme_CW_block_is_MM_at_101
import Theorems.Thm_mme_CW_block_is_MM_at_011
import Theorems.Thm_mme_CW_block_is_MM_at_200
import Theorems.Thm_mme_CW_block_is_MM_at_020
import Theorems.Thm_mme_CW_block_is_MM_at_002
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks

open MME MME.DWZFourthElementaryMM
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open MME.DWZFourthPublicOrdinary181
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthPrescribedZ181
open BigOperators Module
open MME
open DWZComponentRestriction DWZRestrictedValue
open DWZFourthScalarLedger
open DWZFourthScalarLedgerInduction
open DWZFourthTensorLedger
open scoped Classical

theorem properLedgerPrescribedZEndpoints_of_pointwise :
    ∀ {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3} (data : LedgerPrescribedZData tensorAt) (tau : ℝ) (h : ProperLedgerPrescribedZEndpointsPointwise data tau),
    ProperLedgerPrescribedZEndpoints data tau :=
  mme_dwz_fourth_prescribedZ_181_integration.{u}.1

theorem headline :
    ∀ {K : Type u} [Field K] (hstructure : Fourth181StructuralPremise K),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) :=
  mme_dwz_fourth_prescribedZ_181_integration.{u}.2

end MME.DWZFourthPrescribedZ181
namespace MME.DWZFourthPublicOrdinary181
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open scoped Classical

theorem properSixEndpointsPointwise_of_partition :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpublic : PublicComplementSixEndpoints tensorAt tau) (hpositive : PositiveFourthSixEndpoints tensorAt tau),
    ProperSixEndpointsPointwise tensorAt tau :=
  mme_dwz_fourth_public_ordinary_181_reduction.{u}.1

theorem canonicalQ5_solution :
    ∀ {K : Type u} [Field K] (hpublic : PublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hpositive : PositiveFourthSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)) (hfinal : FinalSixExtraction (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
    HasSixSymmetricTauValueAtLeast
      (StothersFourth.cwFourthObj K 5)
      (790643 / 1000000 : ℝ) (240101 / 100 : ℝ) :=
  mme_dwz_fourth_public_ordinary_181_reduction.{u}.2

end MME.DWZFourthPublicOrdinary181
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
namespace MME.DWZFourthTensorLedger
open MME
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

theorem tensorAt_component :
    ∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K) (index : Fin 180),
    tensorAt api (componentLedgerIndex index) =
      api.component (componentSpecAt index).address :=
  mme_dwz_fourth_tensor_ledger_metadata.{u}.1

theorem tensorAt_final_eq_cwFourthObj5 :
    ∀ {K : Type u} [Field K] (api : Q5CanonicalComponents K),
    tensorAt api ⟨180, by norm_num⟩ = api.cwFourthObj5 :=
  mme_dwz_fourth_tensor_ledger_metadata.{u}.2

end MME.DWZFourthTensorLedger

-- The platform states these with a `match` on `Fin 3`; this development writes the same
-- function as a vector literal.  A hand-written `match` elaborates to its own auxiliary
-- constant, so no rewrite can bridge them syntactically; `convert` diffs the two terms
-- and leaves the pointwise equality, which is `rfl` at each concrete index.

private theorem blockMM_110 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1 5 1)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![1, 1, 0]) := by
  convert mme_CW_block_is_MM_at_110 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

private theorem blockMM_101 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 5 1 1)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![1, 0, 1]) := by
  convert mme_CW_block_is_MM_at_101 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

private theorem blockMM_011 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1 1 5)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![0, 1, 1]) := by
  convert mme_CW_block_is_MM_at_011 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

private theorem blockMM_200 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![2, 0, 0]) := by
  convert mme_CW_block_is_MM_at_200 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

private theorem blockMM_020 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![0, 2, 0]) := by
  convert mme_CW_block_is_MM_at_020 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

private theorem blockMM_002 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwCanonicalGrading 5 (K := K)).blockSubtensor ![0, 0, 2]) := by
  convert mme_CW_block_is_MM_at_002 (K := K) 5 using 3
  rename_i i
  fin_cases i <;> rfl

namespace MME.DWZFourthElementaryMM

private theorem log20Lower_le : (log20Lower : Real) ≤ Real.log 20 := by
  have h5 := (mme_log_interval_of_auto_scaled_rational
    (5 / 4) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (20 : Real) =
      Real.log ((5 / 4 : Rat) : Real) + 4 * Real.log 2 := by
    rw [show (20 : Real) = (((5 / 4 : Rat) : Real) * 2 ^ 4) by norm_num,
      Real.log_mul (by norm_num : (((5 / 4 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 4 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log20Lower, log2Lower] using
    add_le_add h5
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 4))

private theorem log154Lower_le : (log154Lower : Real) ≤ Real.log 154 := by
  have h77 := (mme_log_interval_of_auto_scaled_rational
    (77 / 64) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (154 : Real) =
      Real.log ((77 / 64 : Rat) : Real) + 7 * Real.log 2 := by
    rw [show (154 : Real) = (((77 / 64 : Rat) : Real) * 2 ^ 7) by norm_num,
      Real.log_mul (by norm_num : (((77 / 64 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 7 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log154Lower, log2Lower] using
    add_le_add h77
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 7))

private theorem log560Lower_le : (log560Lower : Real) ≤ Real.log 560 := by
  have h35 := (mme_log_interval_of_auto_scaled_rational
    (35 / 32) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (560 : Real) =
      Real.log ((35 / 32 : Rat) : Real) + 9 * Real.log 2 := by
    rw [show (560 : Real) = (((35 / 32 : Rat) : Real) * 2 ^ 9) by norm_num,
      Real.log_mul (by norm_num : (((35 / 32 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 9 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log560Lower, log2Lower] using
    add_le_add h35
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 9))

private theorem log931Lower_le : (log931Lower : Real) ≤ Real.log 931 := by
  have h931 := (mme_log_interval_of_auto_scaled_rational
    (931 / 512) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (931 : Real) =
      Real.log ((931 / 512 : Rat) : Real) + 9 * Real.log 2 := by
    rw [show (931 : Real) = (((931 / 512 : Rat) : Real) * 2 ^ 9) by norm_num,
      Real.log_mul (by norm_num : (((931 / 512 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 9 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log931Lower, log2Lower] using
    add_le_add h931
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 9))

private theorem log5Lower_le : (log5Lower : Real) ≤ Real.log 5 := by
  have h5 := (mme_log_interval_of_auto_scaled_rational
    (5 / 4) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (5 : Real) =
      Real.log ((5 / 4 : Rat) : Real) + 2 * Real.log 2 := by
    rw [show (5 : Real) = (((5 / 4 : Rat) : Real) * 2 ^ 2) by norm_num,
      Real.log_mul (by norm_num : (((5 / 4 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 2 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log5Lower, log2Lower] using
    add_le_add h5
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 2))

private theorem log10Lower_le : (log10Lower : Real) ≤ Real.log 10 := by
  have h5 := (mme_log_interval_of_auto_scaled_rational
    (5 / 4) 0 8 (by norm_num) (by norm_num)).1
  have h2 := (mme_log_interval_of_auto_scaled_rational
    2 0 8 (by norm_num) (by norm_num)).1
  have heq : Real.log (10 : Real) =
      Real.log ((5 / 4 : Rat) : Real) + 3 * Real.log 2 := by
    rw [show (10 : Real) = (((5 / 4 : Rat) : Real) * 2 ^ 3) by norm_num,
      Real.log_mul (by norm_num : (((5 / 4 : Rat) : Real) ≠ 0))
        (by norm_num : (2 : Real) ^ 3 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log10Lower, log2Lower] using
    add_le_add h5
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : Real) ≤ 3))

private theorem fourthBoundaryMMSize_pos (address : ComponentAddress) :
    0 < fourthBoundaryMMSize address := by
  cases address with
  | base i j k => simp [fourthBoundaryMMSize, fourthBoundaryOrbitIndex]
  | square i j k => simp [fourthBoundaryMMSize, fourthBoundaryOrbitIndex]
  | fourth i j k =>
      simp only [fourthBoundaryMMSize]
      generalize fourthBoundaryOrbitIndex (.fourth i j k) = r
      rcases r with _ | _ | _ | _ | r <;> simp

private theorem fourthBoundaryLogLower_le (address : ComponentAddress) :
    (fourthBoundaryLogLower address : Real) ≤
      Real.log (fourthBoundaryMMSize address : Real) := by
  cases address with
  | base i j k => simp [fourthBoundaryLogLower, fourthBoundaryOrbitIndex,
      fourthBoundaryMMSize]
  | square i j k => simp [fourthBoundaryLogLower, fourthBoundaryOrbitIndex,
      fourthBoundaryMMSize]
  | fourth i j k =>
      simp only [fourthBoundaryLogLower, fourthBoundaryMMSize]
      generalize fourthBoundaryOrbitIndex (.fourth i j k) = r
      rcases r with _ | _ | _ | _ | r
      · simp
      · exact log20Lower_le
      · exact log154Lower_le
      · exact log560Lower_le
      · exact log931Lower_le

/-- Exact finite audit of all 24 stored boundary rates. -/
private theorem all_boundary_rates_below_log_lower :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.fourthElementaryBoundary →
        properLedgerRate index ≤
          (790643 / 1000000 : Rat) *
            fourthBoundaryLogLower (componentSpecAt index).address := by
  decide +kernel

private theorem atomicMMSize_pos (address : ComponentAddress) :
    0 < atomicMMSize address := by
  cases address with
  | base i j k =>
      by_cases h : i.val = 2 ∨ j.val = 2 ∨ k.val = 2 <;>
        simp [atomicMMSize, h]
  | square i j k => simp [atomicMMSize]
  | fourth i j k => simp [atomicMMSize]

private theorem squareElementaryMMSize_pos (address : ComponentAddress) :
    0 < squareElementaryMMSize address := by
  cases address with
  | base i j k => simp [squareElementaryMMSize]
  | square i j k =>
      by_cases h : i.val = 4 ∨ j.val = 4 ∨ k.val = 4 <;>
        simp [squareElementaryMMSize, h]
  | fourth i j k => simp [squareElementaryMMSize]

private theorem atomicLogLower_le (address : ComponentAddress) :
    (atomicLogLower address : Real) ≤ Real.log (atomicMMSize address : Real) := by
  simp only [atomicLogLower]
  split_ifs with h
  · rw [h]
    simp
  · have hsize : atomicMMSize address = 5 := by
      cases address with
      | base i j k =>
          by_cases hc : i.val = 2 ∨ j.val = 2 ∨ k.val = 2
          · simp [atomicMMSize, hc] at h
          · simp [atomicMMSize, hc]
      | square i j k => simp [atomicMMSize] at h
      | fourth i j k => simp [atomicMMSize] at h
    simpa [hsize] using log5Lower_le

private theorem squareElementaryLogLower_le (address : ComponentAddress) :
    (squareElementaryLogLower address : Real) ≤
      Real.log (squareElementaryMMSize address : Real) := by
  simp only [squareElementaryLogLower]
  split_ifs with h
  · rw [h]
    simp
  · have hsize : squareElementaryMMSize address = 10 := by
      cases address with
      | base i j k => simp [squareElementaryMMSize] at h
      | square i j k =>
          by_cases hc : i.val = 4 ∨ j.val = 4 ∨ k.val = 4
          · simp [squareElementaryMMSize, hc] at h
          · simp [squareElementaryMMSize, hc]
      | fourth i j k => simp [squareElementaryMMSize] at h
    simpa [hsize] using log10Lower_le

private theorem all_atomic_rates_below_log_lower :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.atomicExactMM →
        properLedgerRate index ≤
          (790643 / 1000000 : Rat) *
            atomicLogLower (componentSpecAt index).address := by
  decide +kernel

private theorem all_square_elementary_rates_below_log_lower :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.squareElementaryBoundary →
        properLedgerRate index ≤
          (790643 / 1000000 : Rat) *
            squareElementaryLogLower (componentSpecAt index).address := by
  decide +kernel

private theorem hasTauValue_mono_endpoint
    {K : Type u} [Field K]
    {T : TensorObj K 3} {tau A B : Real}
    (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : HasTauValueAtLeast T tau B) :
    HasTauValueAtLeast T tau A := by
  rcases hB with ⟨hB0, hB⟩
  refine ⟨hA, ?_⟩
  intro epsilon hepsilon
  exact (hB epsilon hepsilon).mono (fun N hN ↦ by
    rcases hN with ⟨k, a, b, c, hrestrict, hweight⟩
    refine ⟨k, a, b, c, hrestrict, ?_⟩
    by_cases hepsilonOne : epsilon ≤ 1
    · have hpow : A ^ N ≤ B ^ N := pow_le_pow_left₀ hA hAB N
      exact (mul_le_mul_of_nonneg_right hpow
        (sub_nonneg.mpr hepsilonOne)).trans hweight
    · have hleft : A ^ N * (1 - epsilon) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hA N)
          (sub_nonpos.mpr (le_of_not_ge hepsilonOne))
      exact hleft.trans (Finset.sum_nonneg
        (fun i _ ↦ Real.rpow_nonneg (by positivity) tau)))

private theorem rpow_six_eq_volume (d : Nat) (tau : Real) :
    ((d : Real) ^ tau) ^ (6 : Nat) =
      (((d ^ 6 : Nat) : Real) ^ tau) := by
  calc
    ((d : Real) ^ tau) ^ (6 : Nat) =
        ((d : Real) ^ tau) ^ (6 : Real) :=
      (Real.rpow_natCast _ 6).symm
    _ = (d : Real) ^ (tau * 6) :=
      (Real.rpow_mul (by positivity) tau 6).symm
    _ = (d : Real) ^ (6 * tau) := by rw [mul_comm]
    _ = ((d : Real) ^ (6 : Nat)) ^ tau :=
      Real.rpow_natCast_mul (by positivity) 6 tau
    _ = (((d ^ 6 : Nat) : Real) ^ tau) := by rw [Nat.cast_pow]

/-- Any restriction from an MM tensor inherits its six-symmetric endpoint.
The sixth power is generated internally from the ordinary MM volume. -/
private theorem mmRestrict_hasSix_of_endpoint
    {K : Type u} [Field K]
    (T : TensorObj K 3) (n m p : Nat) (tau V : Real)
    (hV : 0 ≤ V)
    (hendpoint : V ≤ (((n * m * p : Nat) : Real) ^ tau))
    (hrestrict : TensorObj.Restrict (MMObj K n m p) T) :
    HasSixSymmetricTauValueAtLeast T tau V := by
  let d := n * m * p
  have hcyclic := mme_MMObj_cyclicSymmetrization_iso (K := K) n m p
  have hswappedCyclic : TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization (MMObj K n m p)))
      (MMObj K d d d) := by
    exact (TensorObj.permObj_isomorphic swapFirstTwoPerm hcyclic).trans
      (mme_MMObj_permObj_swapFirstTwo d d d)
  have hsixIso : TensorObj.Isomorphic
      (sixSymmetrization (MMObj K n m p))
      (MMObj K (d * d) (d * d) (d * d)) := by
    exact (TensorQ.mul_respects_iso hcyclic hswappedCyclic).trans
      (MMObj_kron_iso d d d d d d)
  have hmm := mme_MMObj_tau_value (K := K) (d * d) (d * d) (d * d) tau
  have hsixMM : HasTauValueAtLeast
      (sixSymmetrization (MMObj K n m p)) tau
      ((((d * d) * (d * d) * (d * d) : Nat) : Real) ^ tau) :=
    mme_HasTauValueAtLeast_mono_restrict hsixIso.2 hmm
  have hendpointSix : V ^ 6 ≤
      ((((d * d) * (d * d) * (d * d) : Nat) : Real) ^ tau) := by
    calc
      V ^ 6 ≤ (((d : Real) ^ tau) ^ 6) := by
        exact pow_le_pow_left₀ hV (by simpa [d] using hendpoint) 6
      _ = (((d ^ 6 : Nat) : Real) ^ tau) := rpow_six_eq_volume d tau
      _ = ((((d * d) * (d * d) * (d * d) : Nat) : Real) ^ tau) := by
        congr 2
        ring
  unfold HasSixSymmetricTauValueAtLeast
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_sixSymmetrization_restrict hrestrict)
    (hasTauValue_mono_endpoint (pow_nonneg hV 6) hendpointSix hsixMM)

private theorem fourthBoundaryIndexSet_card : fourthBoundaryIndexSet.card = 24 := by
  decide +kernel

private theorem nonBoundaryPublicComplementIndexSet_card :
    nonBoundaryPublicComplementIndexSet.card = 135 := by
  decide +kernel

private theorem centralSquarePublicComplementIndexSet_card :
    centralSquarePublicComplementIndexSet.card = 120 := by
  decide +kernel

private theorem boundaryRotate_eq_fixedModeRelabel
    (rho : Fin 3 → Fin 9) :
    boundaryRotate rho =
      StothersFourth.fixedModeRelabel cyclicPerm rho := by
  funext i
  fin_cases i <;> rfl

private theorem boundarySwap_eq_fixedModeRelabel
    (rho : Fin 3 → Fin 9) :
    boundarySwap rho =
      StothersFourth.fixedModeRelabel swapFirstTwoPerm rho := by
  funext i
  fin_cases i <;> rfl

private theorem fourthBoundary_address_is_fourth :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.fourthElementaryBoundary →
        ∃ i j k : Fin 9,
          (componentSpecAt index).address = .fourth i j k := by
  decide +kernel

private theorem fourthBoundary_address_orbit :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.fourthElementaryBoundary →
        ∃ oriented : Fin 8, ∃ rotation : Fin 3,
          componentFourthType (componentSpecAt index).address =
            boundaryOrbitEntry oriented rotation := by
  decide +kernel

private theorem fourthBoundary_size_of_orbit :
    ∀ (index : Fin 180)
      (_hrow : publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.fourthElementaryBoundary)
      (oriented : Fin 8) (rotation : Fin 3),
      componentFourthType (componentSpecAt index).address =
          boundaryOrbitEntry oriented rotation →
        fourthBoundaryMMSize (componentSpecAt index).address =
          boundaryRepSize oriented := by
  decide +kernel

private theorem MMVolumeRestricts.rotate
    {K : Type u} [Field K] (rho : Fin 3 → Fin 9) (volume : Nat)
    (h : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor rho)
      volume) :
    MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (boundaryRotate rho)) volume := by
  rcases h with ⟨n, m, p, hvolume, hrestrict⟩
  refine ⟨p, n, m, ?_, ?_⟩
  · calc p * n * m = n * m * p := by ac_rfl
         _ = volume := hvolume
  · exact TensorObj.Restrict.trans
      (MMObj_permObj_cyclic (K := K) n m p).2
      (TensorObj.Restrict.trans
        (TensorObj.permObj_restrict cyclicPerm hrestrict)
        (by
          simpa [boundaryRotate_eq_fixedModeRelabel] using
            (mme_stothers_cwFourth_cyclic_block_iso
              (K := K) 5 rho).2))

private theorem MMVolumeRestricts.swap
    {K : Type u} [Field K] (rho : Fin 3 → Fin 9) (volume : Nat)
    (h : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor rho)
      volume) :
    MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (boundarySwap rho)) volume := by
  rcases h with ⟨n, m, p, hvolume, hrestrict⟩
  refine ⟨p, m, n, ?_, ?_⟩
  · calc p * m * n = n * m * p := by ac_rfl
         _ = volume := hvolume
  · exact TensorObj.Restrict.trans
      (mme_MMObj_permObj_swapFirstTwo (K := K) n m p).2
      (TensorObj.Restrict.trans
        (TensorObj.permObj_restrict swapFirstTwoPerm hrestrict)
        (by
          simpa [boundarySwap_eq_fixedModeRelabel] using
            (mme_stothers_cwFourth_swapped_block_iso
              (K := K) 5 rho).2))

private theorem boundaryOrientedRep_restricts
    {K : Type u} [Field K] :
    ∀ oriented : Fin 8,
      MMVolumeRestricts
        ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
          (boundaryOrientedRep oriented))
        (boundaryRepSize oriented) := by
  intro oriented
  rcases mme_stothers_elementary_fourth_constituent_MM_restrict
      (K := K) 5 with ⟨h008, h017, h026, h035, h044⟩
  have h008' : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (StothersFourth.cwFourthBlockType 0 0 8)) 1 :=
    ⟨1, 1, 1, by norm_num,
      by simpa [StothersFourth.cwFourthConstituent] using h008⟩
  have h017' : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (StothersFourth.cwFourthBlockType 0 1 7)) 20 :=
    ⟨1, 1, 20, by norm_num,
      by simpa [StothersFourth.cwFourthConstituent] using h017⟩
  have h026' : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (StothersFourth.cwFourthBlockType 0 2 6)) 154 :=
    ⟨1, 1, 154, by norm_num,
      by simpa [StothersFourth.cwFourthConstituent] using h026⟩
  have h035' : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (StothersFourth.cwFourthBlockType 0 3 5)) 560 :=
    ⟨1, 1, 560, by norm_num,
      by simpa [StothersFourth.cwFourthConstituent] using h035⟩
  have h044' : MMVolumeRestricts
      ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (StothersFourth.cwFourthBlockType 0 4 4)) 931 :=
    ⟨1, 1, 931, by norm_num,
      by simpa [StothersFourth.cwFourthConstituent] using h044⟩
  fin_cases oriented
  · simpa [boundaryOrientedRep, boundaryRepSize] using h008'
  · simpa [boundaryOrientedRep, boundaryRepSize] using h017'
  · simpa [boundaryOrientedRep, boundaryRepSize] using
      MMVolumeRestricts.swap
        (StothersFourth.cwFourthBlockType 0 1 7) 20 h017'
  · simpa [boundaryOrientedRep, boundaryRepSize] using h026'
  · simpa [boundaryOrientedRep, boundaryRepSize] using
      MMVolumeRestricts.swap
        (StothersFourth.cwFourthBlockType 0 2 6) 154 h026'
  · simpa [boundaryOrientedRep, boundaryRepSize] using h035'
  · simpa [boundaryOrientedRep, boundaryRepSize] using
      MMVolumeRestricts.swap
        (StothersFourth.cwFourthBlockType 0 3 5) 560 h035'
  · simpa [boundaryOrientedRep, boundaryRepSize] using h044'

private theorem boundaryOrbitEntry_restricts
    {K : Type u} [Field K] (oriented : Fin 8) :
    ∀ rotation : Fin 3,
      MMVolumeRestricts
        ((StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
          (boundaryOrbitEntry oriented rotation))
        (boundaryRepSize oriented) := by
  intro rotation
  fin_cases rotation
  · exact boundaryOrientedRep_restricts oriented
  · exact MMVolumeRestricts.rotate (boundaryOrientedRep oriented)
      (boundaryRepSize oriented) (boundaryOrientedRep_restricts oriented)
  · exact MMVolumeRestricts.rotate
      (boundaryRotate (boundaryOrientedRep oriented))
      (boundaryRepSize oriented)
      (MMVolumeRestricts.rotate (boundaryOrientedRep oriented)
        (boundaryRepSize oriented) (boundaryOrientedRep_restricts oriented))

private theorem canonicalQ5_tensorAt_boundary_eq
    {K : Type u} [Field K] (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.fourthElementaryBoundary) :
    tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)
        (properLedgerIndex index) =
      (StothersFourth.cwFourthCanonicalGrading K 5).blockSubtensor
        (componentFourthType (componentSpecAt index).address) := by
  rcases fourthBoundary_address_is_fourth index hrow with
    ⟨i, j, k, haddress⟩
  have hindex : properLedgerIndex index = componentLedgerIndex index := by
    apply Fin.ext
    rfl
  rw [hindex, tensorAt_component, haddress]
  rfl

/-- The public five-representative theorem plus cyclic and transposition
equivariance discharges the complete 24-row structural bundle for the literal
q=5 tensor family. -/
private theorem canonicalQ5FourthBoundaryMMRestrictions
    {K : Type u} [Field K] :
    FourthBoundaryMMRestrictions
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) := by
  intro index hrow
  rcases fourthBoundary_address_orbit index hrow with
    ⟨oriented, rotation, horbit⟩
  have hsource := boundaryOrbitEntry_restricts (K := K) oriented rotation
  have hsize := fourthBoundary_size_of_orbit index hrow oriented rotation horbit
  rcases hsource with ⟨n, m, p, hvolume, hrestrict⟩
  refine ⟨n, m, p, hvolume.trans hsize.symm, ?_⟩
  rw [canonicalQ5_tensorAt_boundary_eq index hrow, horbit]
  exact hrestrict

private theorem atomic_address_rep :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.atomicExactMM →
        ∃ rep : Fin 6,
          componentBaseType (componentSpecAt index).address = atomicRep rep := by
  decide +kernel

private theorem atomic_size_of_rep :
    ∀ (index : Fin 180)
      (_hrow : publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.atomicExactMM) (rep : Fin 6),
      componentBaseType (componentSpecAt index).address = atomicRep rep →
        atomicMMSize (componentSpecAt index).address = atomicRepSize rep := by
  decide +kernel

private theorem squareElementary_address_rep :
    ∀ index : Fin 180,
      publicCoverageTier (componentSpecAt index) =
          PublicCoverageTier.squareElementaryBoundary →
        ∃ rep : Fin 9,
          componentSquareType (componentSpecAt index).address =
            squareElementaryRep rep := by
  decide +kernel

private theorem squareElementary_size_of_rep :
    ∀ (index : Fin 180)
      (_hrow : publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.squareElementaryBoundary) (rep : Fin 9),
      componentSquareType (componentSpecAt index).address =
          squareElementaryRep rep →
        squareElementaryMMSize (componentSpecAt index).address =
          squareElementaryRepSize rep := by
  decide +kernel

private theorem atomicRep_restricts
    {K : Type u} [Field K] :
    ∀ rep : Fin 6,
      MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (atomicRep rep))
        (atomicRepSize rep) := by
  intro rep
  fin_cases rep
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![1, 1, 0])) 5 from
        ⟨1, 5, 1, by norm_num,
          by simpa using (blockMM_110 (K := K))⟩)
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![1, 0, 1])) 5 from
        ⟨5, 1, 1, by norm_num,
          by simpa using (blockMM_101 (K := K))⟩)
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![0, 1, 1])) 5 from
        ⟨1, 1, 5, by norm_num,
          by simpa using (blockMM_011 (K := K))⟩)
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![2, 0, 0])) 1 from
        ⟨1, 1, 1, by norm_num,
          by simpa using (blockMM_200 (K := K))⟩)
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![0, 2, 0])) 1 from
        ⟨1, 1, 1, by norm_num,
          by simpa using (blockMM_020 (K := K))⟩)
  · simpa [atomicRep, atomicRepSize] using
      (show MMVolumeRestricts
        ((cwCanonicalGrading 5 (K := K)).blockSubtensor (![0, 0, 2])) 1 from
        ⟨1, 1, 1, by norm_num,
          by simpa using (blockMM_002 (K := K))⟩)

private theorem squareElementaryRep_restricts
    {K : Type u} [Field K] :
    ∀ rep : Fin 9,
      MMVolumeRestricts
        ((cwSquareCanonicalGrading K 5).blockSubtensor
          (squareElementaryRep rep))
        (squareElementaryRepSize rep) := by
  intro rep
  rcases mme_CW_square_canonical_elementary_blocks (K := K) 5 with
    ⟨_hsupport, h004, h040, h400, h013, h031, h103, h301, h130, h310,
      _h022, _h202, _h220⟩
  fin_cases rep
  · exact ⟨1, 1, 1, by simp [squareElementaryRepSize], h004⟩
  · exact ⟨1, 1, 1, by simp [squareElementaryRepSize], h040⟩
  · exact ⟨1, 1, 1, by simp [squareElementaryRepSize], h400⟩
  · exact ⟨1, 1, 10, by simp [squareElementaryRepSize],
      by simpa using h013⟩
  · exact ⟨1, 1, 10, by simp [squareElementaryRepSize],
      by simpa using h031⟩
  · exact ⟨10, 1, 1, by simp [squareElementaryRepSize],
      by simpa using h103⟩
  · exact ⟨10, 1, 1, by simp [squareElementaryRepSize],
      by simpa using h301⟩
  · exact ⟨1, 10, 1, by simp [squareElementaryRepSize],
      by simpa using h130⟩
  · exact ⟨1, 10, 1, by simp [squareElementaryRepSize],
      by simpa using h310⟩

private theorem canonicalQ5_tensorAt_atomic_eq
    {K : Type u} [Field K] (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.atomicExactMM) :
    tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)
        (properLedgerIndex index) =
      (cwCanonicalGrading 5 (K := K)).blockSubtensor
        (componentBaseType (componentSpecAt index).address) := by
  have haddress : ∃ i j k : Fin 3,
      (componentSpecAt index).address = .base i j k := by
    revert index
    decide +kernel
  rcases haddress with ⟨i, j, k, haddress⟩
  have hindex : properLedgerIndex index = componentLedgerIndex index := by
    apply Fin.ext
    rfl
  rw [hindex, tensorAt_component, haddress]
  rfl

private theorem canonicalQ5_tensorAt_squareElementary_eq
    {K : Type u} [Field K] (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.squareElementaryBoundary) :
    tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)
        (properLedgerIndex index) =
      (cwSquareCanonicalGrading K 5).blockSubtensor
        (componentSquareType (componentSpecAt index).address) := by
  have haddress : ∃ i j k : Fin 5,
      (componentSpecAt index).address = .square i j k := by
    revert index
    decide +kernel
  rcases haddress with ⟨i, j, k, haddress⟩
  have hindex : properLedgerIndex index = componentLedgerIndex index := by
    apply Fin.ext
    rfl
  rw [hindex, tensorAt_component, haddress]
  rfl

private theorem canonicalQ5AtomicMMRestrictions
    {K : Type u} [Field K] :
    AtomicMMRestrictions
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) := by
  intro index hrow
  rcases atomic_address_rep index hrow with ⟨rep, hrep⟩
  have hsource := atomicRep_restricts (K := K) rep
  have hsize := atomic_size_of_rep index hrow rep hrep
  rcases hsource with ⟨n, m, p, hvolume, hrestrict⟩
  refine ⟨n, m, p, hvolume.trans hsize.symm, ?_⟩
  rw [canonicalQ5_tensorAt_atomic_eq index hrow, hrep]
  exact hrestrict

private theorem canonicalQ5SquareElementaryMMRestrictions
    {K : Type u} [Field K] :
    SquareElementaryMMRestrictions
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)) := by
  intro index hrow
  rcases squareElementary_address_rep index hrow with ⟨rep, hrep⟩
  have hsource := squareElementaryRep_restricts (K := K) rep
  have hsize := squareElementary_size_of_rep index hrow rep hrep
  rcases hsource with ⟨n, m, p, hvolume, hrestrict⟩
  refine ⟨n, m, p, hvolume.trans hsize.symm, ?_⟩
  rw [canonicalQ5_tensorAt_squareElementary_eq index hrow, hrep]
  exact hrestrict

private theorem fourthBoundary_exp_le_MM_endpoint
    (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.fourthElementaryBoundary) :
    Real.exp (properLedgerRate index : Real) ≤
      (fourthBoundaryMMSize (componentSpecAt index).address : Real) ^
        (790643 / 1000000 : Real) := by
  have hrateRat := all_boundary_rates_below_log_lower index hrow
  have hrate : (properLedgerRate index : Real) ≤
      (((790643 / 1000000 : Rat) *
        fourthBoundaryLogLower (componentSpecAt index).address : Rat) :
          Real) := by
    exact_mod_cast hrateRat
  have hlog := fourthBoundaryLogLower_le (componentSpecAt index).address
  have hmul :
      (790643 / 1000000 : Real) *
          (fourthBoundaryLogLower (componentSpecAt index).address : Real) ≤
        (790643 / 1000000 : Real) *
          Real.log (fourthBoundaryMMSize
            (componentSpecAt index).address : Real) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  rw [Real.rpow_def_of_pos (by
    exact_mod_cast fourthBoundaryMMSize_pos (componentSpecAt index).address)]
  apply Real.exp_le_exp.mpr
  calc
    (properLedgerRate index : Real) ≤
        (((790643 / 1000000 : Rat) *
          fourthBoundaryLogLower (componentSpecAt index).address : Rat) :
            Real) := hrate
    _ = (790643 / 1000000 : Real) *
          (fourthBoundaryLogLower (componentSpecAt index).address : Real) := by
      norm_num
    _ ≤ (790643 / 1000000 : Real) *
          Real.log (fourthBoundaryMMSize
            (componentSpecAt index).address : Real) := hmul
    _ = Real.log (fourthBoundaryMMSize
          (componentSpecAt index).address : Real) *
          (790643 / 1000000 : Real) := by ring

private theorem fourthBoundarySixEndpoints_of_MMRestrictions
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3)
    (hMM : FourthBoundaryMMRestrictions tensorAt) :
    FourthBoundarySixEndpoints tensorAt := by
  intro index hrow
  rcases hMM index hrow with ⟨n, m, p, hsize, hrestrict⟩
  apply mmRestrict_hasSix_of_endpoint
      (tensorAt (properLedgerIndex index)) n m p
      (790643 / 1000000 : Real)
      (Real.exp (properLedgerRate index : Real))
  · exact (Real.exp_pos _).le
  · simpa [hsize] using fourthBoundary_exp_le_MM_endpoint index hrow
  · exact hrestrict

private theorem atomic_exp_le_MM_endpoint
    (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.atomicExactMM) :
    Real.exp (properLedgerRate index : Real) ≤
      (atomicMMSize (componentSpecAt index).address : Real) ^
        (790643 / 1000000 : Real) := by
  have hrateRat := all_atomic_rates_below_log_lower index hrow
  have hrate : (properLedgerRate index : Real) ≤
      (((790643 / 1000000 : Rat) *
        atomicLogLower (componentSpecAt index).address : Rat) : Real) := by
    exact_mod_cast hrateRat
  have hlog := atomicLogLower_le (componentSpecAt index).address
  have hmul := mul_le_mul_of_nonneg_left hlog
    (by norm_num : (0 : Real) ≤ 790643 / 1000000)
  rw [Real.rpow_def_of_pos (by
    exact_mod_cast atomicMMSize_pos (componentSpecAt index).address)]
  apply Real.exp_le_exp.mpr
  calc
    (properLedgerRate index : Real) ≤
        (((790643 / 1000000 : Rat) *
          atomicLogLower (componentSpecAt index).address : Rat) : Real) := hrate
    _ = (790643 / 1000000 : Real) *
          (atomicLogLower (componentSpecAt index).address : Real) := by norm_num
    _ ≤ (790643 / 1000000 : Real) *
          Real.log (atomicMMSize (componentSpecAt index).address : Real) := hmul
    _ = Real.log (atomicMMSize (componentSpecAt index).address : Real) *
          (790643 / 1000000 : Real) := by ring

private theorem squareElementary_exp_le_MM_endpoint
    (index : Fin 180)
    (hrow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.squareElementaryBoundary) :
    Real.exp (properLedgerRate index : Real) ≤
      (squareElementaryMMSize (componentSpecAt index).address : Real) ^
        (790643 / 1000000 : Real) := by
  have hrateRat := all_square_elementary_rates_below_log_lower index hrow
  have hrate : (properLedgerRate index : Real) ≤
      (((790643 / 1000000 : Rat) *
        squareElementaryLogLower (componentSpecAt index).address : Rat) :
          Real) := by
    exact_mod_cast hrateRat
  have hlog := squareElementaryLogLower_le (componentSpecAt index).address
  have hmul := mul_le_mul_of_nonneg_left hlog
    (by norm_num : (0 : Real) ≤ 790643 / 1000000)
  rw [Real.rpow_def_of_pos (by
    exact_mod_cast squareElementaryMMSize_pos
      (componentSpecAt index).address)]
  apply Real.exp_le_exp.mpr
  calc
    (properLedgerRate index : Real) ≤
        (((790643 / 1000000 : Rat) *
          squareElementaryLogLower (componentSpecAt index).address : Rat) :
            Real) := hrate
    _ = (790643 / 1000000 : Real) *
          (squareElementaryLogLower (componentSpecAt index).address : Real) := by
      norm_num
    _ ≤ (790643 / 1000000 : Real) *
          Real.log (squareElementaryMMSize
            (componentSpecAt index).address : Real) := hmul
    _ = Real.log (squareElementaryMMSize
          (componentSpecAt index).address : Real) *
          (790643 / 1000000 : Real) := by ring

private theorem atomicSixEndpoints_of_MMRestrictions
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (hMM : AtomicMMRestrictions tensorAt) :
    AtomicSixEndpoints tensorAt := by
  intro index hrow
  rcases hMM index hrow with ⟨n, m, p, hsize, hrestrict⟩
  apply mmRestrict_hasSix_of_endpoint
      (tensorAt (properLedgerIndex index)) n m p
      (790643 / 1000000 : Real)
      (Real.exp (properLedgerRate index : Real))
  · exact (Real.exp_pos _).le
  · simpa [hsize] using atomic_exp_le_MM_endpoint index hrow
  · exact hrestrict

private theorem squareElementarySixEndpoints_of_MMRestrictions
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (hMM : SquareElementaryMMRestrictions tensorAt) :
    SquareElementarySixEndpoints tensorAt := by
  intro index hrow
  rcases hMM index hrow with ⟨n, m, p, hsize, hrestrict⟩
  apply mmRestrict_hasSix_of_endpoint
      (tensorAt (properLedgerIndex index)) n m p
      (790643 / 1000000 : Real)
      (Real.exp (properLedgerRate index : Real))
  · exact (Real.exp_pos _).le
  · simpa [hsize] using squareElementary_exp_le_MM_endpoint index hrow
  · exact hrestrict

private theorem nonBoundaryPublicComplement_of_elementary_MM
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3)
    (hatomic : AtomicMMRestrictions tensorAt)
    (hsquare : SquareElementaryMMRestrictions tensorAt)
    (hcentral : CentralSquarePublicComplementSixEndpoints tensorAt) :
    NonBoundaryPublicComplementSixEndpoints tensorAt := by
  intro index hnotPositive hnotFourthBoundary
  by_cases hatomicRow : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.atomicExactMM
  · exact atomicSixEndpoints_of_MMRestrictions tensorAt hatomic index hatomicRow
  · by_cases hsquareRow : publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.squareElementaryBoundary
    · exact squareElementarySixEndpoints_of_MMRestrictions tensorAt hsquare
        index hsquareRow
    · exact hcentral index hnotPositive hnotFourthBoundary hatomicRow hsquareRow

/-- Closes all 24 elementary boundary endpoints, leaving exactly the other
135 rows of `PublicComplementSixEndpoints`. -/
private theorem headline
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3)
    (hMM : FourthBoundaryMMRestrictions tensorAt)
    (hother : NonBoundaryPublicComplementSixEndpoints tensorAt) :
    PublicComplementSixEndpoints tensorAt
      (790643 / 1000000 : Real) := by
  intro index hnotPositive
  by_cases hboundary : publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.fourthElementaryBoundary
  · exact fourthBoundarySixEndpoints_of_MMRestrictions tensorAt hMM
      index hboundary
  · exact hother index hnotPositive hboundary

/-- Canonical q=5 specialization: all 24 elementary fourth-boundary rows are
fully discharged from public theorems.  Exactly the other 135 public-complement
rows remain as a single endpoint bundle. -/
private theorem canonicalQ5_solution
    {K : Type u} [Field K]
    (hother : NonBoundaryPublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))) :
    PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : Real) := by
  exact headline _ canonicalQ5FourthBoundaryMMRestrictions hother

/-- Strongest exact-MM specialization: all 39 atomic, square-boundary, and
fourth-boundary rows are fully discharged.  The one remaining premise contains
exactly 120 central/coupled square rows. -/
private theorem canonicalQ5_solution_120
    {K : Type u} [Field K]
    (hcentral : CentralSquarePublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))) :
    PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : Real) := by
  let tensorFamily :=
    tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K)
  apply headline tensorFamily canonicalQ5FourthBoundaryMMRestrictions
  exact nonBoundaryPublicComplement_of_elementary_MM tensorFamily
    canonicalQ5AtomicMMRestrictions
    canonicalQ5SquareElementaryMMRestrictions hcentral

end MME.DWZFourthElementaryMM

theorem solution :
    ∀ {K : Type u} [Field K] (hcentral : CentralSquarePublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))),
    PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : Real) :=
  canonicalQ5_solution_120
