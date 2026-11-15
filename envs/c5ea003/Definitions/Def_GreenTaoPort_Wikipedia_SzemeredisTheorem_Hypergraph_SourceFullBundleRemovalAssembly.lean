-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:14:57.618931+00:00
-- url     : https://prove2.me/theorems/15d77881-fb03-49ad-a944-0c077fb8b717
-- title:
--   Explicit reserves for source-full bundle removal
-- statement:
--   For the initial ordered-configuration bundle, the removal horizon is the reverse-doubling horizon at rank zero. This is the largest edge-count range queried by the later counting recurrence.
--
--   The density-cleaning allowance is $\min(\varepsilon,1)$ divided by four times one plus the number of positive ordered subfaces. The per-step reserve is $1/(4(rH+1))$, where $H$ is the horizon, and the square-root defect coefficient is one eighth of this reserve.
--
--   Given a scale ceiling $M$ and density budget $\delta$, the final count threshold is one half of $(\delta/(M+1))^s$, where $s$ is the number of positive ordered faces. These total formulas fix the numerical reserves before the finite ambient vertex type is chosen.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalAssembly.lean#L25-L170

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
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
# Source-full bundle-counting removal assembly

This file joins the ambient-independent source-full regularity plan to the
rankwise bundle-counting theorem and the source-full bad-base deletion family.
The selected regularity scale is clipped to the finite rank horizon.  Since
the selected scales decrease with rank while `sourceBundleDensity` decreases
with its scale, the resulting density schedule increases with rank; hence its
bundle prefix floor is exactly its rank-zero value.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Ambient-independent scalar budgets -/

/-- The largest edge horizon queried by the reverse-doubling recurrence. -/
noncomputable def sourceBundleRemovalHorizon (k r : ℕ) : ℕ :=
  bundleReverseDoublingHorizon r
    (orderedConfigurationInitialBundle k r).edges.card 0

/-- Each positive subface spends two copies of this allowance: one for
low density and one for its source-full defect. -/
noncomputable def sourceBundleRemovalDensityBudget
    (ε : ℝ) (r : ℕ) : ℝ :=
  min ε 1 /
    (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ)

/-- The per-step reserve in the explicit reverse-doubling envelope. -/
noncomputable def sourceBundleRemovalStep (k r : ℕ) : ℝ :=
  1 /
    (4 * (r * sourceBundleRemovalHorizon k r + 1 : ℕ) : ℕ)

/-- The square-root defect coefficient; the factor eight leaves room for
both halves of every one-edge counting increment. -/
noncomputable def sourceBundleRemovalKappa (k r : ℕ) : ℝ :=
  sourceBundleRemovalStep k r / 8

























/-! ## A uniform count threshold from the bounded scale ceiling -/

noncomputable def sourceBundleRemovalCountThreshold
    (k r ceiling : ℕ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceBundleDensity δ ceiling ^
      Fintype.card (PositiveOrderedFace k r)



/-! ## End-to-end source-full ordered removal -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.sourceBundleRemovalCountThreshold.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceBundleRemovalDensityBudget.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceBundleRemovalHorizon.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceBundleRemovalStep.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


