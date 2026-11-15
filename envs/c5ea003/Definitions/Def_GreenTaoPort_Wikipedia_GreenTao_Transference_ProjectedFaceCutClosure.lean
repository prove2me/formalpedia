-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:51.010836+00:00
-- url     : https://prove2.me/theorems/9503be05-2ffe-4433-92a0-09934d7da4bc
-- title:
--   Deactivating a selected sparse face
-- statement:
--   For $k$ face colours, an activity mask is a Boolean function on $\operatorname{Fin}(k)$. Deactivating colour $j$ sets its value to false and leaves every other colour unchanged. This update records the colours that remain sparse after the densification step at $j$; it does not alter any face weights itself.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ProjectedFaceCutClosure.lean#L607-L611

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Closure of projected face-cut discrepancy

A recursive relative-simplex comparison has two logically separate closure
steps.

* Truncating a projected incident product at one is stable against every
  lower-face cut test.  The loss is exactly the square-root moment loss from
  each side.
* If all simplex edges are already bounded, edgewise face-cut discrepancy is
  stable under projection.  The proof inserts the requested lower-face cut
  product into the distinguished edge and applies the bounded simplex
  comparison theorem.

For a genuinely sparse system the second statement cannot be applied:
the other edge weights occurring in the telescope need not be bounded by
one.  The theorem
`HasProjectedMajorantMoments.faceCutDiscrepancyLe_projectedPairing_of_raw`
therefore isolates the precise remaining hypothesis, namely face-cut
discrepancy of the *untruncated* projected pairings.  This is the residual
which an iterated sparse densification argument must propagate.

The first section also records the exact finite-product consequence of the
generalized-convolution mixture API.  It identifies the one-variable
nonlinear closure already available from dense-model duality; no extra
analytic hypothesis is introduced here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Multiplicative closure of generalized-convolution tests -/



/-! ## Nonlinear truncation closure -/





/-! ## The exact raw projected residual -/





/-! ## Bounded algebraic closure under projection -/

























/-! ## AP specialization and active-mask transition -/

/-- Remove one chosen colour from the set of still-sparse faces. -/
def deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k) :
    Fin k → Bool :=
  fun i => if i = j then false else active i



















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.deactivateFace.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


