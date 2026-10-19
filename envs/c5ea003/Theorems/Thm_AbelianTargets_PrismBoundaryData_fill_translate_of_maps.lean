-- Prove2me | Theorems.Thm_AbelianTargets_PrismBoundaryData_fill_translate_of_maps
-- name    : AbelianTargets.PrismBoundaryData.fill_translate_of_maps
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:40:15.86488+00:00
-- url     : https://prove2.me/theorems/d900afbf-4c66-45bb-82db-690c48043ca0
-- title:
--   Prism fillings commute with simultaneous translation and isometric transport
-- statement:
--   Let $R$ be an integer rectangle in dimension $d$, with positive width in coordinate $i$, and let $a\in\mathbb Z^d$. Let $Z,W$ be metric spaces and $e:Z\to W$ an isometric equivalence. Let $F:\partial R\to Z$ and $G:\partial(R+a)\to W$ be continuous prism-boundary data with constant lower and upper $i$-faces $p,q$ and $p',q'$, respectively, finite path-time bounds $S,S'$ and transverse bounds $B,B'$. Suppose $H,H'$ are basepoint-fixing controlled contractions to $p,p'$ with common track and joint bounds $D,J\ge0$. Assume
--   $$e(p)=p',\quad e(q)=q',\quad H'(e(v),t)=e(H(v,t)),\quad G(z+a)=e(F(z)).$$
--   Then their contraction-cone fillings satisfy
--   $$\operatorname{Fill}(G,H')(z+a)=e(\operatorname{Fill}(F,H)(z))\qquad(z\in R).$$
--   The constants $S,B$ and $S',B'$ need not agree.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/PrismFillNaturality.lean, lines 51–83; SHA256 41ffd4d7ec975c214e65c01020ef1fb7a72758d72a2bb1a5989956da731abb3d.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
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
open scoped NNReal unitInterval
namespace AbelianTargets.PrismBoundaryData
end AbelianTargets.PrismBoundaryData
open AbelianTargets
open AbelianTargets.PrismBoundaryData
variable {d : ℕ} {Z W : Type*} [MetricSpace Z] [MetricSpace W]
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {p' q' : W}
variable {D J S B S' B' : ℝ≥0}

theorem AbelianTargets.PrismBoundaryData.fill_translate_of_maps (F : PrismBoundaryData R i p q S B)
    (H : ControlledContraction p D J) (a : Fin d→ℤ) (e : Z≃ᵢW)
    (G : PrismBoundaryData (R.translate a) i p' q' S' B')
    (H' : ControlledContraction p' D J) (hp : e p=p') (hq : e q=q')
    (hH : ∀v t,H'.map (e v,t)=e (H.map (v,t)))
    (hmap : ∀z : CellBoundaryDomain R,G.map (R.translateBoundaryPoint a z)=e (F.map z))
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    G.fill H' (by simpa [RectangularCell.translate] using hi) (R.translateClosedPoint a z)=
      e (F.fill H hi z) := by sorry
