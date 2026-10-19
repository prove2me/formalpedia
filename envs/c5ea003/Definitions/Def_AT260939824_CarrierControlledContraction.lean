-- Prove2me | Definitions.Def_AT260939824_CarrierControlledContraction
-- name    : AT260939824_CarrierControlledContraction
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:22:59.038584+00:00
-- url     : https://prove2.me/theorems/a220f01d-1c16-4814-9c84-0bcfda26f299
-- title:
--   The two-stage interval-carrier contraction map
-- statement:
--   For base $m\ge2$ and positive interval width $R$, take the carrier of height $\lfloor\log_mR\rfloor$. Its height deformation supplies a height-zero endpoint, whose weighted horizontal coordinate is then an input to the realized bottom combing. The bottom-completion family uses reversed combing time to reach the distinguished bottom vertex.
--
--   The assembled map concatenates height deformation and bottom completion, then remains constant at that vertex. Its included endpoint identities say that time zero is the identity on the carrier and time one is the constant distinguished-point map. This is the literal time family used by the controlled-contraction estimates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierControlledContraction.lean, selected declaration lines 16-22, 33-36, 58-66, 79-83, 98-99, 125-129, 131-136; SHA-256 b384a237cd56abeebbb0755c82c8fa158650459e789f7a29253115142955b90c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomCoordinateInverse
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_CurveFamilyStages
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

/-! An actual controlled contraction of the finite triangulated interval
carrier. Every track has logarithmic speed; the joint constant is finite. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def bottomFinish (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : Realization m (Nat.log m R) 0 R × unitInterval) :
    Realization m (Nat.log m R) 0 R :=
  realizedBottomCombing m hm R hR
    (bottomCoordinate (Nat.log m R) R
      (heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R (z.1,1)).1,
      unitInterval.symm z.2)



@[simp] theorem bottomFinish_one (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    bottomFinish m hm R hR (p,1)=point (carrierBase (Nat.log m R) R) := by
  simp [bottomFinish]





theorem base_height_zero {m : Nat} (K R : ℕ) (v : CarrierVertex K 0 R)
    (hv : 0 < (point (carrierBase K R) : Realization m K 0 R).1.mass v) : v.1.2=0 := by
  classical
  have he : v=carrierBase K R := by
    by_contra h
    change 0 < (Probability.dirac (carrierBase K R)).mass v at hv
    simp [Probability.dirac_mass,h] at hv
  rw [he]
  rfl



def carrierContractionStages (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ℕ → Realization m (Nat.log m R) 0 R × unitInterval → Realization m (Nat.log m R) 0 R
  | 0 => heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R
  | 1 => bottomFinish m hm R hR
  | _+2 => fun _ => point (carrierBase (Nat.log m R) R)





def carrierContractionMap (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :=
  familyHomotopy (carrierContractionStages m hm R hR) 2





@[simp] theorem carrierContractionMap_zero (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) : carrierContractionMap m hm R hR (p,0)=p := by
  change familyCurve _ 2 (0,p)=p
  rw [familyCurve_zero]
  exact heightDeformation_zero (by omega : 1 ≤ m) p

@[simp] theorem carrierContractionMap_one (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    carrierContractionMap m hm R hR (p,1)=point (carrierBase (Nat.log m R) R) := by
  change familyCurve _ (1+1) (1,p)=_
  rw [familyCurve_one]
  exact bottomFinish_one m hm R hR p





end
end AbelianTargets.IntervalCarriers


