-- Prove2me | Definitions.Def_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
-- name    : mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:35:07.562568+00:00
-- url     : https://prove2.me/theorems/92167d85-8ff2-470f-ad5e-9888f74af23f
-- title:
--   The 40 one-hot prescribed-Z ledger endpoints
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_oneHot_40_prescribedZ_endpoints, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Mathlib.Tactic
import Definitions.Def_mme_dwz_fourth_public_component_coverage_data
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_HasPrescribedZSix_of_constant_grade_oneHot
import Definitions.Def_mme_dwz_fourth_six_value_final_node_split_data
import Theorems.Thm_mme_dwz_fourth_six_value_final_node_split

open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger.OneHotEndpoints

/-- Replace the six invalid atomic `[0,0]` sentinels by the normalized
one-cell profile `[1,0]`.  All non-atomic rows remain byte-for-byte equal to
the generated ledger data. -/
def normalizedZCounts (metadata : ComponentMetadata) : List Nat :=
  if metadata.method = .atomic then [1, 0] else metadata.zCounts

def normalizedZDenominator (metadata : ComponentMetadata) : Nat :=
  if metadata.method = .atomic then 1 else metadata.zDenominator

/-- Pick the first nonzero cell of a normalized profile.  The fallback in
each branch is its final cell; the one-hot certificate below proves that this
is the unique cell carrying the whole denominator on every selected row. -/
def activeGradeOf (address : ComponentAddress) (counts : List Nat) :
    Fin address.zWidth :=
  match address with
  | .base .. =>
      if counts[0]?.getD 0 != 0 then
        ⟨0, by decide +kernel +revert⟩
      else ⟨1, by decide +kernel +revert⟩
  | .square .. =>
      if counts[0]?.getD 0 != 0 then ⟨0, by decide +kernel +revert⟩
      else if counts[1]?.getD 0 != 0 then
        ⟨1, by decide +kernel +revert⟩
      else ⟨2, by decide +kernel +revert⟩
  | .fourth .. =>
      if counts[0]?.getD 0 != 0 then ⟨0, by decide +kernel +revert⟩
      else if counts[1]?.getD 0 != 0 then
        ⟨1, by decide +kernel +revert⟩
      else if counts[2]?.getD 0 != 0 then
        ⟨2, by decide +kernel +revert⟩
      else if counts[3]?.getD 0 != 0 then
        ⟨3, by decide +kernel +revert⟩
      else ⟨4, by decide +kernel +revert⟩

def activeGrade (i : Fin 180) :
    Fin (componentSpecAt i).address.zWidth :=
  activeGradeOf (componentSpecAt i).address
    (normalizedZCounts (componentSpecAt i))

def normalizedZCount (i : Fin 180)
    (a : Fin (componentSpecAt i).address.zWidth) : Nat :=
  (normalizedZCounts (componentSpecAt i))[a.val]?.getD 0

theorem normalizedZDenominator_pos (i : Fin 180) :
    0 < normalizedZDenominator (componentSpecAt i) := by
  decide +kernel +revert

theorem normalizedZCount_sum (i : Fin 180) :
    ∑ a, normalizedZCount i a =
      normalizedZDenominator (componentSpecAt i) := by
  decide +kernel +revert

/-- The exact generated profile on non-atomic rows, with only the documented
atomic sentinel normalization applied. -/
def normalizedZProfile (i : Fin 180) :
    IntegerZSplitProfile (componentSpecAt i).address.zWidth where
  denominator := normalizedZDenominator (componentSpecAt i)
  denominator_pos := normalizedZDenominator_pos i
  count := normalizedZCount i
  count_sum := normalizedZCount_sum i

/-- A row family has the canonical constant grading needed by the reverse
one-hot restriction precisely on the rows selected by the ledger census. -/
def ConstantOnOneHotRows
    {K : Type u} [Field K]
    (ι : Fin 180 → Type u)
    (grade : (i : Fin 180) →
      ι i → Fin (componentSpecAt i).address.zWidth) : Prop :=
  ∀ (i : Fin 180),
    hasOneHotLedgerZProfile (componentSpecAt i) = true →
      ∀ x, grade i x = activeGrade i

/-- The exact ordinary endpoint premise restricted to the forty selected
rows.  This avoids requiring facts about the other 140 components. -/
def OneHotProperSixEndpointsPointwise
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ (i : Fin 180),
    hasOneHotLedgerZProfile (componentSpecAt i) = true →
      HasSixSymmetricTauValueAtLeast
        (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)) tau
        (Real.exp
          (DWZFourthSixFinalSplit.properLedgerRate i : ℝ))

/-! ## Canonical constant choice on the actual component spaces -/
/-- Use the standard noncomputable basis choice on the *actual* Z-space of
each proper ledger tensor.  This is definitionally the same basis-selection
mechanism used by the 181-node integration interface. -/
noncomputable def componentBasisIndex
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (i : Fin 180) : Type u :=
  Module.Free.ChooseBasisIndex K
    ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)

noncomputable def componentBasis
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (i : Fin 180) :
    Basis (componentBasisIndex tensorAt i) K
      ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2) :=
  Module.Free.chooseBasis K
    ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)

/-- On a one-hot row every basis coordinate is assigned its computed active
grade.  Defining the same harmless constant on the other rows keeps this a
single dependent family; those other grades are not used by this theorem. -/
def componentConstantGrade
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (i : Fin 180) :
    componentBasisIndex tensorAt i →
      Fin (componentSpecAt i).address.zWidth :=
  fun _ ↦ activeGrade i

end MME.DWZFourthTensorLedger.OneHotEndpoints


