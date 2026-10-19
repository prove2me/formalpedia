-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.NormalizedContractionFamily.atWidthInterval_shift
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:53:29.483016+00:00
-- url     : https://prove2.me/submissions/811a4dfa-a9ee-49fd-b2d9-ca7f85aa84c0

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierTranslationEquiv
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UniformCarrierContraction
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_VerticalCarrierCollapse
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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
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

-- Preserved source skeleton: AbelianTargets.CanonicalIntervalContractions
section
/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K : ℕ} {A B C D E F : ℤ}







theorem intervalShiftEquiv_comp (a b : ℤ) (hA : A+a=C) (hB : B+a=D)
    (hC : C+b=E) (hD : D+b=F) (p : Realization m K A B) :
    intervalShiftEquiv b hC hD (intervalShiftEquiv a hA hB p)=
      intervalShiftEquiv (a+b) (by omega) (by omega) p := by
  apply Subtype.ext
  simp only [intervalShiftEquiv_val,Probability.push_comp]
  congr 1
  funext v
  apply Subtype.ext
  simp [intervalVertexShift,translate,Function.comp_def,add_assoc]











end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J : ℝ≥0}





end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K S : ℕ} {J : ℝ≥0}





end
end AbelianTargets.IntervalCarriers

end

/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
variable {m K S : ℕ} {J : ℝ≥0}
open AbelianTargets.IntervalCarriers.NormalizedContractionFamily

theorem solution
    (H : NormalizedContractionFamily m K S J) (n : ℕ) (hn : 0<n) (hS : n≤S)
    (A B C D a : ℤ) (hb : (n:ℤ)+A=B) (hA : A+a=C) (hB : B+a=D)
    (p : Realization m K A B) (t : I) :
    (H.atWidthInterval n hn hS C D (by omega)).map (intervalShiftEquiv a hA hB p,t)=
      intervalShiftEquiv a hA hB ((H.atWidthInterval n hn hS A B hb).map (p,t)) := by
  let e₀ : Realization m K 0 n ≃ᵢ Realization m K A B := intervalShiftEquiv A (by simp) hb
  let e₁ : Realization m K A B ≃ᵢ Realization m K C D := intervalShiftEquiv a hA hB
  let e₂ : Realization m K 0 n ≃ᵢ Realization m K C D := intervalShiftEquiv C (by simp) (by omega)
  have hcomp : ∀q,e₁ (e₀ q)=e₂ q := by
    intro q
    dsimp [e₀,e₁,e₂]
    have hh := intervalShiftEquiv_comp A a (by simp : (0:ℤ)+A=A) hb hA hB q
    simpa only [hA] using hh
  have hinv : e₂.symm (e₁ p)=e₀.symm p := by
    apply e₂.injective
    rw [e₂.apply_symm_apply,←hcomp,e₀.apply_symm_apply]
  simp only [atWidthInterval,ControlledContraction.rebase_map,ControlledContraction.transport]
  change e₂ ((H n hn hS).map (e₂.symm (e₁ p),t))=e₁ (e₀ ((H n hn hS).map (e₀.symm p,t)))
  rw [hinv,hcomp]
