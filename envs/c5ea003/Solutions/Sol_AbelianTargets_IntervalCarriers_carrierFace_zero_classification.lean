-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.carrierFace_zero_classification
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:03:59.531376+00:00
-- url     : https://prove2.me/submissions/2e936f7a-b51c-4355-97ca-4ad2d3a6fa74

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
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

set_option autoImplicit false

/-! Literal height-zero carrier faces are single vertices or adjacent
horizontal unit edges. Hence every bottom realization point is exactly
recovered from its barycentric horizontal coordinate. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers

theorem solution {m R : ℕ} {s : Finset Vertex}
    (hs : CarrierFace m 0 0 R s) :
    (∃ n : ℕ,n ≤ R ∧ s ⊆ {((n : ℤ),0)}) ∨
      ∃ n : ℕ,n < R ∧ s ⊆ {((n : ℤ),0),(((n+1 : ℕ) : ℤ),0)} := by
  have hvertex : ∀ v ∈ carrierVertices 0 0 R,∃ n : ℕ,n ≤ R ∧ v=((n : ℤ),0) := by
    intro v hv
    obtain ⟨hv₀,hvR,hvh⟩ := mem_carrierVertices.mp hv
    refine ⟨v.1.toNat,?_,?_⟩
    · have he := Int.toNat_of_nonneg hv₀
      exact_mod_cast (he ▸ hvR)
    · apply Prod.ext
      · exact (Int.toNat_of_nonneg hv₀).symm
      · omega
  have hedge : ∀ u ∈ carrierVertices 0 0 R,∀ v ∈ carrierVertices 0 0 R,
      HorizontalStep m u v → ∃ n : ℕ,n < R ∧
        u=((n : ℤ),0) ∧ v=(((n+1 : ℕ) : ℤ),0) := by
    intro u hu v hv he
    obtain ⟨n,hn,rfl⟩ := hvertex u hu
    have hvR := (mem_carrierVertices.mp hv).2.1
    have he' : v=(((n+1 : ℕ) : ℤ),0) := by simpa [HorizontalStep] using he
    refine ⟨n,?_,rfl,he'⟩
    rw [he'] at hvR
    dsimp only at hvR
    have hnat : n+1 ≤ R := by exact_mod_cast hvR
    omega
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · obtain ⟨n,hn,rfl⟩ := hvertex v hv
    exact Or.inl ⟨n,hn,hsv⟩
  · obtain ⟨hne,hrel | hrel⟩ := he
    · rcases hrel with hhor | hver
      · obtain ⟨n,hn,rfl,rfl⟩ := hedge u hu v hv hhor
        exact Or.inr ⟨n,hn,hsv⟩
      · have hvh := (mem_carrierVertices.mp hv).2.2
        have hh := congrArg Prod.snd hver
        dsimp [VerticalStep] at hh
        omega
    · rcases hrel with hhor | hver
      · obtain ⟨n,hn,rfl,rfl⟩ := hedge v hv u hu hhor
        exact Or.inr ⟨n,hn,by simpa only [Finset.pair_comm] using hsv⟩
      · have huh := (mem_carrierVertices.mp hu).2.2
        have hh := congrArg Prod.snd hver
        dsimp [VerticalStep] at hh
        omega
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    have hh := (Finset.mem_filter.mp hc).2.1
    omega
