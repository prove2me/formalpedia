-- Prove2me | Definitions.Def_AT260939824_CommonHeightCarrierContraction
-- name    : AT260939824_CommonHeightCarrierContraction
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:24:42.409921+00:00
-- url     : https://prove2.me/theorems/80b41e7b-7c0c-44e0-a31f-1dfe0c7fde63
-- title:
--   Common-height carrier contraction data
-- statement:
--   Fix $m\ge2$, $R>0$, and height $T\ge\lfloor\log_mR\rfloor$. The common-height construction combines the height deformation with bottom completion while keeping all values in the original height-$T$ carrier. It starts at the identity and ends at the distinguished bottom point. Height inclusions preserve Dirac vertex points and that basepoint. Its recorded speed is
--
--   $$ 2\max\bigl(T(m+2),\,B(m,R)+2\bigr), $$
--
--   where $B(m,R)$ is the carry-row budget. These definitions allow interval carriers of different widths to share one ambient height.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CommonHeightCarrierContraction.lean, selected declaration lines 15-18, 20-23, 25-28, 30-33, 50-55, 57-60, 69-72, 98-102, 114-115, 117-118, 144-148, 150-155; SHA-256 bfb29d6b8952caa3cdeb9e8c5b37474c15beef0dc1898386a53be847f4d6cc0b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierNesting
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_GeneralCarrierHeightRestriction
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Controlled contractions at a common height, including intervals shorter
than the ambient logarithmic scale. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

theorem carrierInclude_point {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T)
    (v : CarrierVertex K A B) : carrierInclude (m := m) hKT (point v)=point (vertexInclude hKT v) := by
  apply Subtype.ext
  exact Probability.push_dirac _ _

@[simp] theorem carrierInclude_base {m K T R : ℕ} (hKT : K ≤ T) :
    carrierInclude (m := m) hKT (point (carrierBase K R))=point (carrierBase T R) := by
  rw [carrierInclude_point]
  rfl

def bottomEndpointLower (m : ℕ) (hm : 1 ≤ m) (T R : ℕ) (hlog : Nat.log m R ≤ T)
    (p : Realization m T 0 R) : Realization m (Nat.log m R) 0 R :=
  restrictCarrierHeight hm hlog (heightDeformation hm T 0 R (p,1))
    (fun v hv => by rw [heightDeformation_terminal hm p v hv]; exact Nat.zero_le _)

theorem include_bottomEndpointLower (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    carrierInclude hlog (bottomEndpointLower m hm T R hlog p)=heightDeformation hm T 0 R (p,1) :=
  carrierInclude_restrictCarrierHeight hm hlog _ _





@[simp] theorem bottomEndpointLower_base (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) :
    bottomEndpointLower m hm T R hlog (point (carrierBase T R))=point (carrierBase (Nat.log m R) R) := by
  apply (isometry_include (m := m) (A := 0) (B := R) hlog).injective
  rw [include_bottomEndpointLower,carrierInclude_base,
    heightDeformation_fixes_bottom hm _ (base_height_zero _ _)]

def commonHeightBottomFinish (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (z : Realization m T 0 R × unitInterval) : Realization m T 0 R :=
  carrierInclude hlog (bottomFinish m hm R hR
    (bottomEndpointLower m (by omega : 1 ≤ m) T R hlog z.1,z.2))



@[simp] theorem commonHeightBottomFinish_one (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightBottomFinish m hm T R hR hlog (p,1)=point (carrierBase T R) := by
  simp [commonHeightBottomFinish]







def commonHeightStages (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) : ℕ → Realization m T 0 R × unitInterval → Realization m T 0 R
  | 0 => heightDeformation (by omega : 1 ≤ m) T 0 R
  | 1 => commonHeightBottomFinish m hm T R hR hlog
  | _+2 => fun _ => point (carrierBase T R)



def commonHeightSpeed (m T R : ℕ) : ℝ≥0 :=
  2*max ((T : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)

def commonHeightContractionMap (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) := familyHomotopy (commonHeightStages m hm T R hR hlog) 2





@[simp] theorem commonHeightContractionMap_zero (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) : commonHeightContractionMap m hm T R hR hlog (p,0)=p := by
  change familyCurve _ 2 (0,p)=p
  rw [familyCurve_zero]
  exact heightDeformation_zero (by omega : 1 ≤ m) p

@[simp] theorem commonHeightContractionMap_one (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightContractionMap m hm T R hR hlog (p,1)=point (carrierBase T R) := by
  change familyCurve _ (1+1) (1,p)=_
  rw [familyCurve_one]
  exact commonHeightBottomFinish_one m hm T R hR hlog p





end
end AbelianTargets.IntervalCarriers


