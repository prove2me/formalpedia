-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingParameterSelection
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingParameterSelection
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:20:13.222241+00:00
-- url     : https://prove2.me/theorems/fe35a6c7-5ba8-4884-8422-0183af0d8b6a
-- title:
--   Compatible small parameters for polynomial dense modelling and relative counting
-- statement:
--   For a natural rank parameter $r$ and real density and counting reserves, this structure packages a real polynomial together with positive cut, approximation, linear-forms, and cross-correlation errors. The polynomial approximates the positive part on $[-1,1]$.
--
--   Its certificates require the resulting polynomial dense-model error to be nonnegative and below the density reserve, impose the power inequalities converting linear-forms errors into the selected cut and cross errors, and place the explicit relative-counting recurrence at stage $r+2$ below the counting reserve. Thus it records a mutually compatible choice of all numerical data, rather than asserting that arbitrary positive choices work.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingParameterSelection.lean#L268-L306

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingErrorSchedule
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Small parameters for relative counting

The explicit relative-counting recurrence is continuous at the origin, but
the final transference argument also needs an order-theoretic form of this
fact: replacing any of the three nonnegative input errors by a smaller one
cannot enlarge the scheduled error.

This file first proves that monotonicity and then records a diagonal
small-parameter selector.  These lemmas are the numerical core used when the
polynomial dense-model error and the two linear-forms errors are chosen in a
single parameter package.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped Polynomial







/-! ## Polynomial dense-model parameters below one scalar budget -/



/-! ## A complete finite transference package -/

/-- All small numerical data needed to combine polynomial dense modelling
with the explicit relative-counting recurrence. -/
structure RelativeCountingTransferenceParameters
    (r : ℕ) (densityReserve countReserve : ℝ) where
  polynomial : ℝ[X]
  cutError : ℝ
  approximationError : ℝ
  linearFormsError : ℝ
  crossError : ℝ
  cutError_pos : 0 < cutError
  approximationError_pos : 0 < approximationError
  linearFormsError_pos : 0 < linearFormsError
  crossError_pos : 0 < crossError
  approximates :
    ApproximatesPositivePartOnUnitInterval
      polynomial approximationError
  denseModelError_nonneg :
    0 ≤ polynomialDenseModelError
      polynomial cutError approximationError
  denseModelError_lt :
    polynomialDenseModelError
        polynomial cutError approximationError <
      densityReserve
  denseModel_conversion :
    (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
      cutError ^ (2 ^ (r + 1))
  cross_conversion :
    ∀ j : Fin (r + 2),
      (1 + linearFormsError) ^ (2 ^ (r + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (r + 2) j) *
              linearFormsError) ≤
        crossError ^ (2 ^ (r + 1))
  comparisonError_lt :
    relativeCountingErrorSchedule r
        (polynomialDenseModelError
          polynomial cutError approximationError)
        linearFormsError crossError (r + 2) <
      countReserve



/-! ## Instantiating the comparison callback -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.ctorIdx,
    `Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.mk.inj,
    `Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.mk.injEq,
    `Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.noConfusionType
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


