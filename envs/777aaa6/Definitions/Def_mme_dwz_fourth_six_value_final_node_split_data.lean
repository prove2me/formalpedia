-- Prove2me | Definitions.Def_mme_dwz_fourth_six_value_final_node_split_data
-- name    : mme_dwz_fourth_six_value_final_node_split_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:00:38.01405+00:00
-- url     : https://prove2.me/theorems/4683c7a5-5502-449e-b5b5-fd99505deae4
-- title:
--   Splitting the fourth-power ledger into proper rows and one global node
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_six_value_final_node_split, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_scalar_ledger_induction_facade_data
import Theorems.Thm_mme_dwz_fourth_scalar_ledger_induction_facade
import Definitions.Def_mme_six_symmetrized_tau_value

open MME
open MME.DWZFourthScalarLedger
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthSixFinalSplit

/-- Scalar rates stored before the one global ledger node. -/
def properLedgerRates : Array Rat :=
  runRates (ledger.take 180) #[]

/-- The unique global node. -/
def globalLedgerNode : Node :=
  ledger[180]'(by decide +kernel)

theorem properLedgerRates_size : properLedgerRates.size = 180 := by
  decide +kernel

/-- Exact ordinary six-value endpoints for the 180 proper components. -/
def ProperSixEndpoints
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  RateRealizes
    (fun index value ↦
      HasSixSymmetricTauValueAtLeast
        (tensorAtNat tensorAt index) tau value)
    properLedgerRates

/-- The exact scalar rate attached to a proper (non-global) ledger row. -/
def properLedgerRate (index : Fin 180) : Rat :=
  properLedgerRates[index.val]'(by
    rw [properLedgerRates_size]
    exact index.isLt)

def properLedgerIndex (index : Fin 180) : Fin 181 :=
  ⟨index.val, Nat.lt_trans index.isLt (by norm_num)⟩

/-- Pointwise form of `ProperSixEndpoints`.  This is the convenient public
interface for attaching the separate atomic, square, and fourth coarse-block
theorems to their data-driven rows. -/
def ProperSixEndpointsPointwise
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ index : Fin 180,
    HasSixSymmetricTauValueAtLeast
      (tensorAt (properLedgerIndex index)) tau
      (Real.exp (properLedgerRate index : ℝ))

/-- Final-node extraction, with all scalar facts already exposed separately.
An induced-family/direct-sum theorem should discharge precisely this premise. -/
def FinalSixExtraction
    {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ (weighted : Rat) (product : ℝ),
    (∀ term ∈ globalLedgerNode.children, 0 ≤ term.2) →
    weightedPrior properLedgerRates globalLedgerNode.children = some weighted →
    weightedValueProduct properLedgerRates globalLedgerNode.children =
      some product →
    ChildrenRealize
      (fun index value ↦
        HasSixSymmetricTauValueAtLeast
          (tensorAtNat tensorAt index) tau value)
      properLedgerRates globalLedgerNode →
    HasSixSymmetricTauValueAtLeast
      (tensorAtNat tensorAt properLedgerRates.size) tau
      (Real.exp (globalLedgerNode.retainedFloor : ℝ) * product)

end MME.DWZFourthSixFinalSplit


