-- Prove2me | Definitions.Def_AT260939824_CanonicalIntervalContractions
-- name    : AT260939824_CanonicalIntervalContractions
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:27:38.983878+00:00
-- url     : https://prove2.me/theorems/54de7893-2a53-41c0-bad1-79ddbe69fbe1
-- title:
--   Normalized interval contractions and their translates
-- statement:
--   Fix a carrier base $m$, common height $K$, maximum width $S$, and joint bound $J$. A normalized family assigns a controlled contraction to every zero-based carrier interval $[0,R]$ with $0<R\le S$, all with the common speed determined by $m,K$ and common joint bound $J$. Explicit interval isometries transport these data to arbitrary intervals of width $R$.
--
--   The same selected family is retained under translation, supplying coherent contraction data for all atlas cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4–5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CanonicalIntervalContractions.lean, selected declaration lines 12-16, 18-22, 24-29, 42-45, 64-65, 67-77, 87-89, 91-94, 104-110; SHA-256 cc01dd1d372355303d406b778860f637168990e0fc875320e076a01b859e4796. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
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

/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K : ℕ} {A B C D E F : ℤ}

def intervalShiftEquiv (a : ℤ) (hA : A+a=C) (hB : B+a=D) :
    Realization m K A B ≃ᵢ Realization m K C D := by
  subst C
  subst D
  exact realizationTranslationEquiv a

def intervalVertexShift (a : ℤ) (hA : A+a=C) (hB : B+a=D)
    (v : CarrierVertex K A B) : CarrierVertex K C D :=
  ⟨translate a v.val,by
    have hh := (translate_mem_carrierVertices a v.val).mpr v.property
    simpa only [hA,hB] using hh⟩

@[simp] theorem intervalShiftEquiv_val (a : ℤ) (hA : A+a=C) (hB : B+a=D)
    (p : Realization m K A B) :
    (intervalShiftEquiv a hA hB p).val=Probability.push (intervalVertexShift a hA hB) p.val := by
  subst C
  subst D
  rfl



def NormalizedContractionFamily (m K S : ℕ) (J : ℝ≥0) :=
  ∀ (R : ℕ) (hR : 0<R),R≤S →
    ControlledContraction (point (carrierBase K R) : Realization m K 0 R)
      (uniformCarrierSpeed m K) J





def leftBase (K : ℕ) (A B : ℤ) (hAB : A≤B) : CarrierVertex K A B :=
  ⟨(A,0),mem_carrierVertices.mpr ⟨le_rfl,hAB,Nat.zero_le K⟩⟩

theorem intervalShiftEquiv_base (n : ℕ) (A B : ℤ) (hb : (n:ℤ)+A=B)
    (hAB : A≤B) :
    intervalShiftEquiv A (by simp : (0:ℤ)+A=A) hb
      (point (carrierBase K n) : Realization m K 0 n)=point (leftBase K A B hAB) := by
  apply Subtype.ext
  simp only [intervalShiftEquiv_val]
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  congr 1
  apply Subtype.ext
  simp [intervalVertexShift,carrierBase,leftBase,translate]

end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J : ℝ≥0}

def rebase (H : ControlledContraction p D J) (h : p=q) : ControlledContraction q D J := by
  subst q
  exact H

@[simp] theorem rebase_map (H : ControlledContraction p D J) (h : p=q) (z : Z×unitInterval) :
    (H.rebase h).map z=H.map z := by
  subst q
  rfl

end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K S : ℕ} {J : ℝ≥0}

def NormalizedContractionFamily.atWidthInterval (H : NormalizedContractionFamily m K S J)
    (n : ℕ) (hn : 0<n) (hS : n≤S) (A B : ℤ) (hb : (n:ℤ)+A=B) :
    ControlledContraction (point (leftBase K A B (by omega)) : Realization m K A B)
      (uniformCarrierSpeed m K) J :=
  ((H n hn hS).transport (intervalShiftEquiv (A := 0) (B := n) (C := A) (D := B)
    A (by simp) hb)).rebase
    (intervalShiftEquiv_base n A B hb (by omega))



end
end AbelianTargets.IntervalCarriers


