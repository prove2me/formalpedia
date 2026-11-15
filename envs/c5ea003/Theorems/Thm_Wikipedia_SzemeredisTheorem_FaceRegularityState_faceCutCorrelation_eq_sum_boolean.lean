-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_FaceRegularityState_faceCutCorrelation_eq_sum_boolean
-- name    : Wikipedia.SzemeredisTheorem.FaceRegularityState.faceCutCorrelation_eq_sum_boolean
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:22.204988+00:00
-- url     : https://prove2.me/theorems/8ab1f036-fab4-4b07-b5fe-54ac3e81ec44
-- title:
--   Bernoulli expansion of a face-cut correlation
-- statement:
--   For a face-regularity state $S$ on $G^r$, with $G$ finite and having decidable equality, every real-valued $f$ and cut-test family $u$ satisfy the exact identity expressing $S.\mathrm{faceCutCorrelation}(f,u)$ as the sum over all Boolean cut assignments of their Bernoulli assignment weights times the corresponding Boolean face-cut correlations. No boundedness hypothesis on $u$ is required for this identity.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakRegularity.lean#L146-L199

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Weak regularity against lower-face cut tests

For a function on `Fin r → G`, the hypergraph cut tests are products of
`r` functions, with the `i`th factor omitting coordinate `i`.  A Boolean
cut-test family has a support in the full tuple space.  This file connects
those supports to the abstract energy-increment machinery and proves a
genuine finite weak-regularity lemma:

* the output refines the input partition;
* its complexity grows by an ambient-size-independent power of two;
* the residual is small against every `[0,1]`-valued lower-face cut test.

The passage from Boolean to bounded tests is an exact finite Bernoulli
mixture, not an approximation.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.FaceRegularityState

theorem Wikipedia.SzemeredisTheorem.FaceRegularityState.faceCutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by sorry
