-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.bottomFinish_joint
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:04:21.762975+00:00
-- url     : https://prove2.me/submissions/c511ff9b-b961-48d8-b6aa-3b68fdc1a325

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomCoordinateInverse
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_BottomIntervalMap
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCharts
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitBottomData
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
import Definitions.Def_AT260939824_ProbabilityTwoVertices
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathComparison
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_RowSlotScaling
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
import Theorems.Thm_AbelianTargets_FixedSlots_BottomSpliceData_family_joint_lipschitz
import Theorems.Thm_AbelianTargets_FixedSlots_intervalGlue_joint_lipschitz
import Theorems.Thm_AbelianTargets_Probability_weightedCoordinate_lipschitz
import Theorems.Thm_AbelianTargets_familyCurve_joint

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.BottomCoordinateInverse
section
/-! The actual affine bottom interval is inverted by its barycentric
horizontal coordinate, on every singleton and unit bottom edge. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
open scoped BigOperators NNReal unitInterval



theorem bottomCoordinate_lipschitz (K R : ℕ) :
    LipschitzWith (Probability.weightedCoordinateConstant (fun v : CarrierVertex K 0 R =>
      (v.val.1 : ℝ))) (bottomCoordinate K R) :=
  Probability.weightedCoordinate_lipschitz _

















end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.CurveFamilyStages
section
/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section



















theorem familyHomotopy_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (H : ℕ → X × I → Y) (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0))
    (hjoint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (H n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (familyHomotopy H n) := by
  obtain ⟨J,hJ⟩ := familyCurve_joint H hseam hjoint n
  have he : LipschitzWith 1 (fun z : X × I => ((z.2 : ℝ),z.1)) := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    change max (dist x.2 y.2) (dist x.1 y.1) ≤ (1 : ℝ)*max (dist x.1 y.1) (dist x.2 y.2)
    simp only [one_mul,max_comm]
    exact le_rfl
  exact ⟨J,by simpa only [familyHomotopy,Function.comp_def,mul_one] using hJ.comp he⟩



end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CarrierHeightDeformation
section
/-! The actual finite strip is deformed to its literal bottom edges in
logarithmic-height time, with a speed independent of its horizontal size. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section



theorem heightDeformation_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J (heightDeformation hm K A B) :=
  familyHomotopy_joint _ (heightChain hm K A B).seam (heightChain hm K A B).joint K













end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.DigitBottomCombing
section
/-! The actual digit combing of the entire finite bottom interval, with common slots. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section





theorem digitSplice_targetRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    (digitSplice m hm R n hn).carryTarget.vertices = bottomRow m hm R (n+1) (by omega) :=
  (Classical.choose_spec (exists_bottomSpliceData m hm R n hn)).2



theorem digitSplice_one (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R)
    (u : unitInterval) : (digitSplice m hm R n hn).family (1,u) =
    FixedSlots.asPath (bottomRow m hm R (n+1) (by omega)) (carryRowBudget m R+1) u := by
  rw [FixedSlots.BottomSpliceData.family_one,digitSplice_targetRow]
  apply FixedSlots.rowPath_congr
  intro j hj
  unfold FixedSlots.appendRowEndpoint
  split_ifs with hj'
  · rfl
  · have hl := compressedWord_interval_uniform_length m hm R (n+1) (show n+1 ≤ R by omega)
    symm
    apply bottomRow_terminal
    dsimp [carryRowBudget] at hj'
    omega





theorem digitEdgeFamily_match (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n+1 < R)
    (u : unitInterval) : digitEdgeFamily m hm R n (1,u) = digitEdgeFamily m hm R (n+1) (0,u) := by
  rw [digitEdgeFamily_eq m hm R n (by omega),digitEdgeFamily_eq m hm R (n+1) hn,
    digitSplice_one,digitSplice_zero]







theorem bottomCombing_joint_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (bottomCombing m hm R) := by
  apply FixedSlots.intervalGlue_joint_lipschitz
  · intro i hi
    rw [digitEdgeFamily_eq m hm R i (by omega)]
    exact (digitSplice m hm R i (by omega)).family_joint_lipschitz
  · intro i hi u
    exact digitEdgeFamily_match m hm R i (by omega) u









end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.RealizedBottomCombing
section
/-! The logarithmic-speed bottom combing takes values in the actual carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section









theorem realizedBottomCombing_joint_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (realizedBottomCombing m hm R hR) := by
  obtain ⟨J,hJ⟩ := bottomCombing_joint_lipschitz m hm R hR
  refine ⟨J,LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change dist (realizedBottomCombing m hm R hR x).1.mass
    (realizedBottomCombing m hm R hR y).1.mass ≤ _
  rw [realizedBottomCombing_mass,realizedBottomCombing_mass]
  exact hJ.dist_le_mul x y







end
end AbelianTargets.IntervalCarriers

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
/-! An actual controlled contraction of the finite triangulated interval
carrier. Every track has logarithmic speed; the joint constant is finite. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped NNReal

theorem solution (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (bottomFinish m hm R hR) := by
  obtain ⟨Jh,hJh⟩ := heightDeformation_joint (K := Nat.log m R) (A := 0) (B := R) (by omega : 1 ≤ m)
  obtain ⟨Jb,hJb⟩ := realizedBottomCombing_joint_lipschitz m hm R hR
  have hendpoint := hJh.comp ((LipschitzWith.id : LipschitzWith 1 (id : Realization m (Nat.log m R) 0 R → _)).prodMk
    (LipschitzWith.const (1 : unitInterval)))
  have hcoordinate := (bottomCoordinate_lipschitz (Nat.log m R) R).comp
    (isometry_subtype_coe.lipschitz.comp hendpoint)
  have hpair := (hcoordinate.comp LipschitzWith.prod_fst).prodMk
    (lipschitz_interval_symm.comp LipschitzWith.prod_snd)
  refine ⟨Jb * max ((Probability.weightedCoordinateConstant (fun v : CarrierVertex (Nat.log m R) 0 R =>
      (v.val.1 : ℝ)) * (1 * (Jh * max 1 0))) * 1) (1 * 1),?_⟩
  simpa only [bottomFinish,Function.comp_def] using hJb.comp hpair
