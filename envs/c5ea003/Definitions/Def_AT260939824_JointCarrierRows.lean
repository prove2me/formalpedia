-- Prove2me | Definitions.Def_AT260939824_JointCarrierRows
-- name    : AT260939824_JointCarrierRows
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:04:26.986993+00:00
-- url     : https://prove2.me/theorems/50bad7b4-1ee7-48cc-a283-417261f64278
-- title:
--   Carrier row budgets and joint realizations
-- statement:
--   For a finite interval carrier, the bottom vertex at horizontal coordinate zero is a canonical base point. A row budget depending on the base $m$ and interval length $R$ bounds the common-slot realization of bounded combinatorial triangle-row chains. Endpoint identities for directed word paths identify the resulting actual paths, and the row construction provides the required joint Lipschitz realization.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/JointCarrierRows.lean, selected declaration lines 14-27, 33-35, 37-44, 46-47, 49; SHA-256 41dc2801d0c633d2e9e79100de34c897de66f2657f28764a34a981292adba13f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CanonicalRows
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierRowRealization
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContextualCarrierRows
import Definitions.Def_AT260939824_ControlledRowRealization
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedRowRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_FixedSlotPadding
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_RowValidity
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleRowMoves
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

/-! Bounded carrier row certificates have actual jointly Lipschitz realizations. -/

namespace AbelianTargets
open scoped NNReal
noncomputable section

namespace FixedSlots
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

theorem boundedTriangleRows_realize_joint (ι : V → E) {S : Set E} {Δ C : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) (hC : ∀ a b, dist (ι a) (ι b) ≤ C)
    {B : ℕ} {w u : List V} (h : BoundedTriangleRows Face B w u) (x z : V)
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hv : ValidRow Face w) :
    ∃ F : (canonicalRow ι B x z (padRow (B+2) z w) (padRow_head hx _)
      (padRow_last hz _) (padRow_length (h.length_bounds.1.trans (by omega)))).path.Homotopy
      (canonicalRow ι B x z (padRow (B+2) z u)
        (padRow_head (h.head_eq.symm.trans hx) _) (padRow_last (h.last_eq.symm.trans hz) _)
        (padRow_length (h.length_bounds.2.trans (by omega)))).path,
      (∀ t, F t ∈ S) ∧ (∀ r, LipschitzWith (Δ*(B+1)) (F.eval r)) ∧
        ∃ J : ℝ≥0, LipschitzWith J F := by
  exact fixedRowMoves_realize_joint ι hc hC (h.toFixedRows hc.downward (by omega) z hv hz)
    B x z (padRow_head hx _) (padRow_last hz _)
    (padRow_length (h.length_bounds.1.trans (by omega))) (hv.pad hz _)

end FixedSlots

namespace IntervalCarriers

@[simp] theorem WordPath.vertices_head {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : p.vertices.head? = some x := by
  cases p <;> rfl

@[simp] theorem WordPath.vertices_last {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : p.vertices.getLast? = some z := by
  induction p with
  | nil x => rfl
  | cons h p ih =>
    cases p with
    | nil y => rfl
    | cons h' q => simpa only [WordPath.vertices,List.getLast?_cons_cons] using ih

def carrierBase (K R : ℕ) : CarrierVertex K 0 R :=
  ⟨(0,0),mem_carrierVertices.mpr ⟨le_rfl,by positivity,Nat.zero_le _⟩⟩

def carryRowBudget (m R : ℕ) : ℕ := (m+1)*(Nat.log m R+1)+2*m+5



end IntervalCarriers
end
end AbelianTargets


