-- Prove2me | Definitions.Def_mme_dwz_fourth_elementary_MM_six_endpoints_data
-- name    : mme_dwz_fourth_elementary_MM_six_endpoints_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:30:20.083778+00:00
-- url     : https://prove2.me/theorems/0e23597a-0756-485b-bc69-240475563f32
-- title:
--   The 120 elementary matrix-multiplication six-region endpoints
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_elementary_MM_six_endpoints, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_public_ordinary_181_reduction_data
import Theorems.Thm_mme_dwz_fourth_public_ordinary_181_reduction
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_mmobj_mul
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

open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open MME.DWZFourthPublicOrdinary181
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthElementaryMM

def log2Lower : Rat := autoScaledLogLower 2 0 8

def log20Lower : Rat :=
  autoScaledLogLower (5 / 4) 0 8 + 4 * log2Lower

def log154Lower : Rat :=
  autoScaledLogLower (77 / 64) 0 8 + 7 * log2Lower

def log560Lower : Rat :=
  autoScaledLogLower (35 / 32) 0 8 + 9 * log2Lower

def log931Lower : Rat :=
  autoScaledLogLower (931 / 512) 0 8 + 9 * log2Lower

def log5Lower : Rat :=
  autoScaledLogLower (5 / 4) 0 8 + 2 * log2Lower

def log10Lower : Rat :=
  autoScaledLogLower (5 / 4) 0 8 + 3 * log2Lower

/-- Cyclic-orbit representative of an elementary fourth-boundary address. -/
def fourthBoundaryOrbitIndex : ComponentAddress → Nat
  | .fourth i j k =>
      min (i.val + j.val) (min (i.val + k.val) (j.val + k.val))
  | _ => 0

/-- MM volume of the corresponding q=5 elementary constituent. -/
def fourthBoundaryMMSize (address : ComponentAddress) : Nat :=
  match fourthBoundaryOrbitIndex address with
  | 0 => 1
  | 1 => 20
  | 2 => 154
  | 3 => 560
  | _ => 931

def fourthBoundaryLogLower (address : ComponentAddress) : Rat :=
  match fourthBoundaryOrbitIndex address with
  | 0 => 0
  | 1 => log20Lower
  | 2 => log154Lower
  | 3 => log560Lower
  | _ => log931Lower

def atomicMMSize : ComponentAddress → Nat
  | .base i j k => if i.val = 2 ∨ j.val = 2 ∨ k.val = 2 then 1 else 5
  | _ => 1

def atomicLogLower (address : ComponentAddress) : Rat :=
  if atomicMMSize address = 1 then 0 else log5Lower

def squareElementaryMMSize : ComponentAddress → Nat
  | .square i j k => if i.val = 4 ∨ j.val = 4 ∨ k.val = 4 then 1 else 10
  | _ => 1

def squareElementaryLogLower (address : ComponentAddress) : Rat :=
  if squareElementaryMMSize address = 1 then 0 else log10Lower

/-- Exact MM restriction data required at the 24 elementary fourth-boundary
rows.  No numerical endpoint premise is included. -/
def FourthBoundaryMMRestrictions
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.fourthElementaryBoundary →
      ∃ n m p : Nat,
        n * m * p = fourthBoundaryMMSize (componentSpecAt index).address ∧
        TensorObj.Restrict (MMObj K n m p)
          (tensorAt (properLedgerIndex index))

def FourthBoundarySixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.fourthElementaryBoundary →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index))
        (790643 / 1000000 : Real)
        (Real.exp (properLedgerRate index : Real))

def AtomicMMRestrictions
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.atomicExactMM →
      ∃ n m p : Nat,
        n * m * p = atomicMMSize (componentSpecAt index).address ∧
        TensorObj.Restrict (MMObj K n m p)
          (tensorAt (properLedgerIndex index))

def SquareElementaryMMRestrictions
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.squareElementaryBoundary →
      ∃ n m p : Nat,
        n * m * p = squareElementaryMMSize
          (componentSpecAt index).address ∧
        TensorObj.Restrict (MMObj K n m p)
          (tensorAt (properLedgerIndex index))

def AtomicSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.atomicExactMM →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index))
        (790643 / 1000000 : Real)
        (Real.exp (properLedgerRate index : Real))

def SquareElementarySixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) =
        PublicCoverageTier.squareElementaryBoundary →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index))
        (790643 / 1000000 : Real)
        (Real.exp (properLedgerRate index : Real))

/-- The exact 135-row remainder of the public complement. -/
def NonBoundaryPublicComplementSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen →
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthElementaryBoundary →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index))
        (790643 / 1000000 : Real)
        (Real.exp (properLedgerRate index : Real))

/-- After the atomic, square-boundary, and fourth-boundary exact-MM rows have
been discharged, exactly 120 central/coupled square rows remain. -/
def CentralSquarePublicComplementSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) : Prop :=
  ∀ index : Fin 180,
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen →
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthElementaryBoundary →
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.atomicExactMM →
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.squareElementaryBoundary →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (properLedgerIndex index))
        (790643 / 1000000 : Real)
        (Real.exp (properLedgerRate index : Real))

def fourthBoundaryIndexSet : Finset (Fin 180) :=
  Finset.univ.filter (fun index ↦
    publicCoverageTier (componentSpecAt index) =
      PublicCoverageTier.fourthElementaryBoundary)

def nonBoundaryPublicComplementIndexSet : Finset (Fin 180) :=
  Finset.univ.filter (fun index ↦
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen ∧
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthElementaryBoundary)

def centralSquarePublicComplementIndexSet : Finset (Fin 180) :=
  Finset.univ.filter (fun index ↦
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen ∧
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.fourthElementaryBoundary ∧
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.atomicExactMM ∧
    publicCoverageTier (componentSpecAt index) ≠
        PublicCoverageTier.squareElementaryBoundary)

/-! ## Literal boundary-orbit attachment -/
def componentFourthType : ComponentAddress → Fin 3 → Fin 9
  | .fourth i j k => StothersFourth.cwFourthBlockType i j k
  | _ => StothersFourth.cwFourthBlockType 0 0 0

def boundaryRotate (rho : Fin 3 → Fin 9) : Fin 3 → Fin 9 :=
  ![rho 2, rho 0, rho 1]

def boundarySwap (rho : Fin 3 → Fin 9) : Fin 3 → Fin 9 :=
  ![rho 1, rho 0, rho 2]

/-- The eight oriented boundary representatives.  Three cyclic rotations of
each give all 24 elementary fourth addresses. -/
def boundaryOrientedRep : Fin 8 → Fin 3 → Fin 9 :=
  ![StothersFourth.cwFourthBlockType 0 0 8,
    StothersFourth.cwFourthBlockType 0 1 7,
    boundarySwap (StothersFourth.cwFourthBlockType 0 1 7),
    StothersFourth.cwFourthBlockType 0 2 6,
    boundarySwap (StothersFourth.cwFourthBlockType 0 2 6),
    StothersFourth.cwFourthBlockType 0 3 5,
    boundarySwap (StothersFourth.cwFourthBlockType 0 3 5),
    StothersFourth.cwFourthBlockType 0 4 4]

def boundaryRepSize : Fin 8 → Nat :=
  ![1, 20, 20, 154, 154, 560, 560, 931]

def boundaryOrbitEntry (oriented : Fin 8) : Fin 3 → Fin 3 → Fin 9 :=
  ![boundaryOrientedRep oriented,
    boundaryRotate (boundaryOrientedRep oriented),
    boundaryRotate (boundaryRotate (boundaryOrientedRep oriented))]

def MMVolumeRestricts
    {K : Type u} [Field K] (T : TensorObj K 3) (volume : Nat) : Prop :=
  ∃ n m p : Nat,
    n * m * p = volume ∧ TensorObj.Restrict (MMObj K n m p) T

/-! ## Atomic and square-boundary attachment -/
def componentBaseType : ComponentAddress → Fin 3 → Fin 3
  | .base i j k => ![i, j, k]
  | _ => ![0, 0, 0]

def componentSquareType : ComponentAddress → Fin 3 → Fin 5
  | .square i j k => cwSquareBlockType i j k
  | _ => cwSquareBlockType 0 0 0

def atomicRep : Fin 6 → Fin 3 → Fin 3 :=
  ![![1, 1, 0], ![1, 0, 1], ![0, 1, 1],
    ![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]

def atomicRepSize : Fin 6 → Nat := ![5, 5, 5, 1, 1, 1]

def squareElementaryRep : Fin 9 → Fin 3 → Fin 5 :=
  ![cwSquareBlockType 0 0 4,
    cwSquareBlockType 0 4 0,
    cwSquareBlockType 4 0 0,
    cwSquareBlockType 0 1 3,
    cwSquareBlockType 0 3 1,
    cwSquareBlockType 1 0 3,
    cwSquareBlockType 3 0 1,
    cwSquareBlockType 1 3 0,
    cwSquareBlockType 3 1 0]

def squareElementaryRepSize : Fin 9 → Nat :=
  ![1, 1, 1, 10, 10, 10, 10, 10, 10]

end MME.DWZFourthElementaryMM


