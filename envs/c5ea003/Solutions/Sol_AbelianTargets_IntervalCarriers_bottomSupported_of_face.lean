-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.bottomSupported_of_face
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:04:45.294368+00:00
-- url     : https://prove2.me/submissions/05dd5c71-a64b-45aa-8c96-576e2186bc7e

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomCoordinateInverse
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
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
import Theorems.Thm_AbelianTargets_IntervalCarriers_carrierFace_zero_classification

set_option autoImplicit false

/-! Literal height-zero carrier faces are single vertices or adjacent
horizontal unit edges. Hence every bottom realization point is exactly
recovered from its barycentric horizontal coordinate. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers

theorem solution {m K R : ℕ}
    (p : Probability (CarrierVertex K 0 R)) (s : Finset (CarrierVertex K 0 R))
    (hs : CarrierFace m 0 0 R (s.image Subtype.val))
    (hp : p.SupportedOn (s : Set _)) : BottomSupported K R p := by
  rcases carrierFace_zero_classification hs with ⟨n,hn,hsub⟩ | ⟨n,hn,hsub⟩
  · left
    refine ⟨n,hn,?_⟩
    intro v hv
    have hr := hsub (Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩)
    have he : v=bottomVertex K R n hn := Subtype.ext (Finset.mem_singleton.mp hr)
    simp [he]
  · right
    refine ⟨n,hn,?_⟩
    intro v hv
    have hr := hsub (Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with hr | hr
    · have he : v=bottomVertex K R n hn.le := Subtype.ext hr
      simp [he]
    · have he : v=bottomVertex K R (n+1) (by omega) := Subtype.ext hr
      simp [he]
