-- Prove2me | Definitions.Def_AT260939824_AppendedSpliceData
-- name    : AT260939824_AppendedSpliceData
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:12:42.965961+00:00
-- url     : https://prove2.me/theorems/6e058a8c-43e0-42a8-bf98-111e3693dcf7
-- title:
--   Splice data from an appended carrier edge
-- statement:
--   Suppose a valid row runs from $x$ to $p$, an allowable edge joins $p$ to $q$, and its appended row is equipped with an endpoint-fixed carry homotopy contained in $S$. Face-chart, edge-length, time-track, and joint-continuity bounds are explicit inputs. The resulting splice record combines the original row with the supplied carry data.
--
--   It is the geometric interface used for continuous motion of the bottom endpoint across one edge.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AppendedSpliceData.lean, selected declaration lines 11-42; SHA-256 7aa0df4afdec26ac96468a5874fe526980944480ed3d8a8752d9b236bc9ab10a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AppendedEdgeRows
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalRows
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedRowRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_PaddedRowCoordinates
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_RowSlotScaling
import Definitions.Def_AT260939824_RowValidity
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

set_option autoImplicit false

/-! Constructing the complete moving-endpoint data from literal appended edge rows. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

def appendedSpliceData (ι : V → E) {S : Set E} {Δ C : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) (hC : ∀ a b, dist (ι a) (ι b) ≤ C)
    (n : ℕ) (x p q : V) (w : List V)
    (hx : w.head? = some x) (hz : w.getLast? = some p) (hv : ValidRow Face w)
    (hf : Face {p,q}) (hlen : w.length ≤ n+1)
    (R T : BasedRow n (ι x) (ι q))
    (hR : R.vertices = listRow ι q (w++[q]))
    (F : R.path.Homotopy T.path) (hFS : ∀ t, F t ∈ S)
    (hFL : ∀ r, LipschitzWith (Δ*(n+1)) (F.eval r))
    (hFJ : ∃ J : ℝ≥0, LipschitzWith J F) :
    BottomSpliceData n (ι x) (ι p) (ι q) S Δ where
  leftRow := listRow ι p w
  carrySource := R
  carryTarget := T
  left_source := listRow_zero ι hx
  left_target := by
    unfold listRow
    rw [list_getD_terminal hz (n+2) (by omega)]
  left_edges := fun j _ => listRow_edges ι hv hz Δ hc.edge_bound j
  seam_edges := by rw [hR]; exact appended_seam_edges ι hc hv hz hf n hlen
  left_charts := by rw [hR]; exact appended_rows_charts ι hc hv hz hf n hlen
  corresponding_bound := by
    rw [hR]
    exact ⟨C,appended_rows_corresponding_bound ι C hC w p q n⟩
  edge_bound := hc.edge_bound p q hf
  edge_chart := by
    obtain ⟨F,hconv,hsub,hm⟩ := hc.chart _ hf
    exact ⟨F,hconv,hsub,hm p (by simp),hm q (by simp)⟩
  carry := F
  carry_mem := hFS
  carry_speed := hFL
  carry_joint := hFJ

end
end AbelianTargets.FixedSlots


