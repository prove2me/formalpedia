-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:09:18.234248+00:00
-- url     : https://prove2.me/theorems/18bb488e-80bd-4d57-afbc-561a9d861e16
-- title:
--   Local defect and frozen-uniformity predicates for ordered bundles
-- statement:
--   A nonempty occurrence edge determines a canonically ordered projected face and a map from its assignment space to that face's tuple coordinates. The transported defect is the fine conditional density minus the coarse density fixed by the configuration witness. The uniform residual is the coarse atom indicator minus its fine-boundary conditional mean.
--
--   The localized defect multiplies this defect by the full strict-boundary configuration product. Its quantitative predicate requires the mean square to be at most the rank-dependent defect parameter times the actual strict-boundary bundle count, for every closed bundle and selected nonempty maximum-cardinality edge.
--
--   The frozen-uniformity predicate bounds the absolute selected-edge correlation by a common tolerance for every assignment of the complementary occurrence vertices. These are the explicit two analytic requirements used to obtain the maximal-edge counting step.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleConfigurationStep.lean#L49-L247

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
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
# The ordered-configuration one-edge bundle step

This file isolates the last analytic bridge between ordered atom
configurations and Tao's generalized bundle-counting induction.

For a nonempty occurrence edge `g₀`, its bundle projection is a nonempty
base edge of cardinality at most `r`, hence has a canonical positive
ordered face.  Pulling the configuration indicator back to `g₀` then has
the exact mixed decomposition

```
indicator = coarse density + boundary defect + fine-boundary residual.
```

The generalized counting file already turns a boundary-localized square
estimate into the required square-root error and turns frozen correlation
bounds into the required uniform error.  The two predicates below state
exactly the remaining transport obligations.

The localized-defect predicate is deliberately *weighted by the complete
strict-boundary bundle count*.  The existing
`ClosedOrderedAtomConfiguration.IsMixedGood` estimate controls the defect
on the canonical coarse boundary atom.  Since a strict bundle boundary
also contains all lower-rank configuration factors, obtaining the
weighted statement is an additional hypothesis; it does not follow merely
by discarding factors from the unweighted localized mass.

The frozen-uniformity predicate is the combinatorial reindexing statement
that, after the outside occurrence variables are fixed, the remaining
bundle product is a bounded cut test on the selected projected face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical face of a nonempty occurrence edge -/

/-- A nonempty occurrence edge has nonempty projected base edge. -/
theorem projectedEdge_nonempty
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

/-- Every projected occurrence edge has cardinality at most the complex
rank. -/
theorem projectedEdge_card_le
    {K : Type*} [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

/-- The positive ordered face canonically enumerating the projection of a
nonempty occurrence edge. -/
noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

/-- Transport an occurrence-edge tuple first to the projected base edge
and then to its increasing ordered enumeration. -/
noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

/-! ## The transported mixed decomposition -/

/-- The fine-minus-coarse boundary defect on a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

/-- The coarse-upper residual after conditioning on the fine boundary,
transported to a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)





/-! ## The two exact transport obligations -/

/-- The selected defect multiplied by the complete strict-boundary
configuration indicator. -/
noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

/-- Missing weighted localization statement for ordered configurations in
arbitrary closed bundles.

This is stronger than the currently available unweighted localized defect
bound: the right side is the actual strict-boundary bundle count, not the
mass of the containing coarse boundary atom. -/
def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

/-- Missing frozen-cut transport statement for ordered configurations in
arbitrary bundles.  It says precisely that every frozen remainder is a
bounded face cut covered by the common mixed preliminary regularity
tolerance. -/
def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

/-! ## Assembly of the one-edge input -/



end HypergraphBundle

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.orderedConfigurationBundleDefect.congr_simp,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.orderedConfigurationBundleFace.congr_simp,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.orderedConfigurationBundleUniform.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


