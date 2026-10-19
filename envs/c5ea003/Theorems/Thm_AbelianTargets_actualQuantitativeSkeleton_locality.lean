-- Prove2me | Theorems.Thm_AbelianTargets_actualQuantitativeSkeleton_locality
-- name    : AbelianTargets.actualQuantitativeSkeleton_locality
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:49:48.163047+00:00
-- url     : https://prove2.me/theorems/c2d2b6db-34ef-4d8e-ad10-33bc47fc93ab
-- title:
--   The deterministic atlas recursion depends only on the contained cell pattern
-- statement:
--   Let $T,T'$ be integer rectangular tilings in dimension $d$ with the same side bounds. Fix $m,K\in\mathbb N$, a coordinate $i$, positive lower width bounds $\delta_j>0$, upper width bounds $U_j\ge0$, and contraction bounds $D,J\ge0$. Assume every varying coordinate width of a cell in either tiling lies between $\delta_j$ and $U_j$, and choose controlled contractions $H,H'$ to the left carrier endpoint on every positive-$i$-width cell. Fix an integer parent rectangle $P$. Suppose the tilings have exactly the same cells contained in $P$, and their chosen contractions agree on every such common cell. Then for every $n\in\mathbb N$, every common cell $R\subseteq P$ of rank less than $n$, and every $z\in R$,
--   $$F^n_{T,H}(R,z)=F^n_{T',H'}(R,z),$$
--   where $F^n$ is the deterministic quantitative skeleton recursion with the common numerical parameters.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/DeterministicAtlasLocality.lean, lines 13–62; SHA256 f7cb001378f101767d67d273af7bba9d9a8e053b4836646b1843ba4c03197364.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DeterministicQuantitativeAtlas
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T T' : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

theorem AbelianTargets.actualQuantitativeSkeleton_locality
    (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (hlower' : ∀R,R∈T'.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper' : ∀R,R∈T'.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (H' : ∀R,R∈T'.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (P : RectangularCell d)
    (hcells : ∀Q,Q.closedBox⊆P.closedBox → (Q∈T.cells ↔ Q∈T'.cells))
    (hH : ∀Q (hQ : Q∈T.cells) (hQ' : Q∈T'.cells) (hi : Q.lower i<Q.upper i),
      Q.closedBox⊆P.closedBox → H Q hQ hi=H' Q hQ' hi)
    (n : ℕ) : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hR' : R∈T'.cells)
      (hr : R.rank<n) (hRP : R.closedBox⊆P.closedBox) (z : CellClosedDomain R),
      (actualQuantitativeSkeleton δ U D J hδ hlower hupper H n).map R hR hr z=
        (actualQuantitativeSkeleton δ U D J hδ hlower' hupper' H' n).map R hR' hr z := by sorry
