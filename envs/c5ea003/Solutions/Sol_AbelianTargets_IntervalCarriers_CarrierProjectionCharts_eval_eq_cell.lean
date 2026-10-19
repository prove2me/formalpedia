-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.CarrierProjectionCharts.eval_eq_cell
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:53:29.50487+00:00
-- url     : https://prove2.me/submissions/8017aeb4-1bcd-4261-8c1b-1359b1b38d0d

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleChartIntersections
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
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
set_option maxHeartbeats 800000
/-! Global carrier projections assembled from polygon and skeleton charts. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.IntervalCarriers.CarrierProjectionCharts
end AbelianTargets.IntervalCarriers.CarrierProjectionCharts
open AbelianTargets
open AbelianTargets.IntervalCarriers
open AbelianTargets.IntervalCarriers.CarrierProjectionCharts
variable {m K : ℕ} {A B : ℤ} {Z : Type*} [TopologicalSpace Z]

theorem solution (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (p : Realization m K A B) (c : Vertex) (hc : c∈carrierCells m K A B)
    (t : Finset Vertex) (ht : IsFanTriangle m c t) (hp : RawSupported p.1 t) :
    D.eval hm p=D.cell c p.1 := by
  let s := p.1.positiveSupport
  have hs : s∈simplexFaces m K A B := positiveSupport_mem p
  have hps := Probability.supportedOn_positiveSupport p.1
  have hsub : s.image Subtype.val⊆t := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw)
  have hcell : FaceHasCell (m := m) s := ⟨c,hc,t,ht,hsub⟩
  rw [eval,(D.simplicialData hm).eval_eq_chart p s hs hps]
  change D.faceValue s p.1=D.cell c p.1
  rw [faceValue,dif_pos hcell]
  obtain ⟨a,ha,hpa⟩ := hcell.choose_spec.2
  have hpa' := (rawSupported_of_face hps).mono hpa
  by_cases he : hcell.choose=c
  · rw [he]
  · have hsk := shared_cell_skeleton hm ha ht he hpa' hp
    exact (D.cell_skeleton _ hcell.choose_spec.1 _ ha p.1 hpa' hsk).trans
      (D.cell_skeleton c hc t ht p.1 hp hsk).symm
