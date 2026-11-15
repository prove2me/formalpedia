-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_booleanFaceCutSupport_eval
-- name    : Wikipedia.SzemeredisTheorem.booleanFaceCutSupport_eval
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:41:57.632936+00:00
-- url     : https://prove2.me/theorems/f8c4a63e-2804-4514-abf4-5bf4871ca6c3
-- title:
--   A Boolean cut-support indicator is its Boolean test product
-- statement:
--   Let $G$ be finite with decidable equality, let $r\in\mathbb N$, and let $b$ be a Boolean arity-$r$ cut assignment. At every tuple $x\in G^r$, evaluation of its Boolean face-cut support equals the product of the corresponding Boolean cut-test factors at $x$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakRegularity.lean#L42-L71

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

theorem Wikipedia.SzemeredisTheorem.booleanFaceCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by sorry
