-- Prove2me | Definitions.Def_AT260939824_SimplicialSupport
-- name    : AT260939824_SimplicialSupport
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:59:26.68718+00:00
-- url     : https://prove2.me/theorems/683d9541-4429-49d6-a177-17b685c8519c
-- title:
--   Positive supports and downward-closed carrier faces
-- statement:
--   For a probability mass $\mu$ on a finite vertex set $V$, define
--   $$\operatorname{supp}_+(\mu)=\{v\in V:\mu(v)>0\}.$$
--   The mass is supported on this finite set, and any finite set supporting it contains $\operatorname{supp}_+(\mu)$. Interval-carrier simplex faces are downward closed. Consequently, if $\mu$ belongs to the geometric realization of an interval carrier, its actual positive support is itself one of the carrier's simplex faces. This supplies a canonical face for evaluating glued carrier maps.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SimplicialSupport.lean, selected declaration lines 8-19, 22-29; SHA-256 815b5ba2ae5b472ddd795b7ba71b80287239be52ba973eab2b27ae36f3c1eeb3. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
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

namespace AbelianTargets
noncomputable section
namespace Probability
variable {V : Type*} [Fintype V]
def positiveSupport (p : Probability V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => 0 < p.mass v)
@[simp] theorem mem_positiveSupport (p : Probability V) (v : V) :
    v ∈ p.positiveSupport ↔ 0 < p.mass v := by
  classical
  simp [positiveSupport]
theorem supportedOn_positiveSupport (p : Probability V) :
    p.SupportedOn (p.positiveSupport : Set V) := fun v hv => (mem_positiveSupport p v).mpr hv
theorem positiveSupport_subset (p : Probability V) {s : Finset V}
    (hp : p.SupportedOn (s : Set V)) : p.positiveSupport ⊆ s := by
  intro v hv; exact hp v ((mem_positiveSupport p v).mp hv)
end Probability
namespace IntervalCarriers
theorem simplexFaces_downward {m K : ℕ} {A B : ℤ} {s t : Finset (CarrierVertex K A B)}
    (hs : s ∈ simplexFaces m K A B) (ht : t ⊆ s) : t ∈ simplexFaces m K A B := by
  apply (mem_simplexFaces t).mpr
  exact ((mem_simplexFaces s).mp hs).downward (Finset.image_subset_image ht)
theorem positiveSupport_mem {m K : ℕ} {A B : ℤ} (p : Realization m K A B) :
    p.1.positiveSupport ∈ simplexFaces m K A B := by
  obtain ⟨s,hs,hp⟩ := p.2
  exact simplexFaces_downward hs (p.1.positiveSupport_subset hp)
end IntervalCarriers
end
end AbelianTargets


