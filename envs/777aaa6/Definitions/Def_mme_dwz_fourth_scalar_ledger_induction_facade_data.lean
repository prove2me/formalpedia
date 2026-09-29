-- Prove2me | Definitions.Def_mme_dwz_fourth_scalar_ledger_induction_facade_data
-- name    : mme_dwz_fourth_scalar_ledger_induction_facade_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T04:58:34.000073+00:00
-- url     : https://prove2.me/theorems/e3f82d1c-f28a-4dee-a8d4-3f4989ee0d5b
-- title:
--   Data-driven induction over the fourth-power scalar ledger
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_scalar_ledger_induction_facade, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data
import Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin
import Definitions.Def_mme_tensor_rank

open MME.DWZFourthScalarLedger
open MME
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthScalarLedgerInduction

/-- `rates` realizes tensor-value lower bounds when every stored logarithmic
rate is interpreted by exponentiation.  The natural-number index is the
component's position in the append-only scalar ledger. -/
def RateRealizes (ValueAtLeast : Nat → ℝ → Prop) (rates : Array Rat) : Prop :=
  ∀ (index : Nat) (rate : Rat), rates[index]? = some rate →
    ValueAtLeast index (Real.exp (rate : ℝ))

/-- The exact array of rates produced by replaying a list of scalar nodes. -/
def runRates : List Node → Array Rat → Array Rat
  | [], prior => prior
  | node :: tail, prior => runRates tail (prior.push node.rateFloor)

/-- The sole tensor-specific interface required by the data-driven induction.
A consumer supplies this from the finite common-length theorem, witness
powering, the component restriction, and the finite `bigAdd` aggregation
bridge.  All arithmetic premises are extracted from `nodeAccepts`. -/
def NodeClosure (ValueAtLeast : Nat → ℝ → Prop) : Prop :=
  ∀ (prior : Array Rat) (node : Node) (weighted : Rat),
    (∀ term ∈ node.children, 0 ≤ term.2) →
    weightedPrior prior node.children = some weighted →
    node.rateFloor ≤ weighted + node.retainedFloor →
    RateRealizes ValueAtLeast prior →
    ValueAtLeast prior.size (Real.exp (node.rateFloor : ℝ))

def exactRates : Array Rat := runRates ledger #[]

section TensorFamily

/-- Total indexing adapter for a fixed family of the 181 reachable component
tensors.  On the exact ledger traversal every index is already below 181;
the remainder makes the facade total away from that traversal. -/
def tensorAtNat {K : Type u} [Field K]
    (tensorAt : Fin 181 → TensorObj K 3) (index : Nat) : TensorObj K 3 :=
  tensorAt ⟨index % 181, Nat.mod_lt _ (by norm_num)⟩

/-- Product form of the weighted child rates.  Rational coefficients become
real exponents, exactly matching the power/common-length interpretation. -/
noncomputable def weightedValueProduct (prior : Array Rat) :
    List (Prod Nat Rat) → Option ℝ
  | [] => some 1
  | (index, coefficient) :: tail => do
      let rate ← prior[index]?
      let rest ← weightedValueProduct prior tail
      pure ((Real.exp (rate : ℝ)) ^ (coefficient : ℝ) * rest)

/-- Only the values of children actually referenced by a node are exposed to
the tensor extraction premise. -/
def ChildrenRealize (ValueAtLeast : Nat → ℝ → Prop)
    (prior : Array Rat) (node : Node) : Prop :=
  ∀ term ∈ node.children,
    ∃ rate, prior[term.1]? = some rate ∧
      ValueAtLeast term.1 (Real.exp (rate : ℝ))

/-- Faithful one-node tensor interface.  Its intended implementation uses
the prescribed-Z finite common-physical-length theorem, the finite-witness
power theorem, and a mode-disjoint `bigAdd` restriction/extraction.  Notice
that it assumes no scalar inequality: those are supplied by the checked
ledger. -/
def TensorRecursiveExtraction
    {K : Type u} [Field K]
    (SixValueAtLeast : TensorObj K 3 → ℝ → ℝ → Prop)
    (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) : Prop :=
  ∀ (prior : Array Rat) (node : Node) (weighted : Rat) (product : ℝ),
    (∀ term ∈ node.children, 0 ≤ term.2) →
    weightedPrior prior node.children = some weighted →
    weightedValueProduct prior node.children = some product →
    ChildrenRealize
      (fun index value =>
        SixValueAtLeast (tensorAtNat tensorAt index) tau value) prior node →
    SixValueAtLeast (tensorAtNat tensorAt prior.size) tau
      (Real.exp (node.retainedFloor : ℝ) * product)

end TensorFamily

end MME.DWZFourthScalarLedgerInduction


