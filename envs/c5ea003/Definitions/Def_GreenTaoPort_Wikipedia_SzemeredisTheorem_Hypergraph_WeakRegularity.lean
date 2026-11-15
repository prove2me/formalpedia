-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:54:07.98621+00:00
-- url     : https://prove2.me/theorems/f0d38297-f116-48e6-aca5-491e61791324
-- title:
--   Weak face-cut regularity of partition residuals
-- statement:
--   A Boolean lower-face assignment determines the finite set of full tuples on which every selected deleted-coordinate condition is true. For a finite face partition state and a real function $f$, the face-cut correlation is the normalized mean of the partition residual $f-\mathbb E[f\mid P]$ multiplied by a lower-face cut-test product.
--
--   Weak face-cut regularity at tolerance $\varepsilon$ requires the absolute value of this correlation to be at most $\varepsilon$ for every cut-test family with values in $[0,1]$. The definition does not require $f$ itself to be bounded.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakRegularity.lean#L25-L208

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Lean
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The full-tuple support of a Boolean lower-face cut-test family. -/
noncomputable def booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) :
    BooleanCutTest (Fin r → G) := by
  classical
  exact Finset.univ.filter fun x =>
    ∀ i, b ⟨i, eraseCoordinate i x⟩ = true













namespace FaceRegularityState

/-- Correlation of a regularity residual with a lower-face product test. -/
noncomputable def faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x => S.residual f x * cutTestProduct u x





/-- Weak cut regularity of one face function. -/
def IsFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |S.faceCutCorrelation f u| ≤ ε









end FaceRegularityState

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.booleanFaceCutSupport.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


