-- Prove2me | solution 1 for AbelianTargets.IntervalCarriers.exists_uniformCarrierContractions
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:08:17.176919+00:00
-- url     : https://prove2.me/submissions/7121339f-be0c-47cc-b0fb-2fd55105df55

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
import Definitions.Def_AT260939824_CarrierHeightCut
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierNesting
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
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
import Definitions.Def_AT260939824_ProbabilityTwoVertices
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathComparison
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
import Theorems.Thm_AbelianTargets_FixedSlots_correctedCarry_path_time_lipschitz
import Theorems.Thm_AbelianTargets_FixedSlots_intervalGlue_on_unit
import Theorems.Thm_AbelianTargets_IntervalCarriers_bottomFinish_joint
import Theorems.Thm_AbelianTargets_IntervalCarriers_bottomSupported_of_face
import Theorems.Thm_AbelianTargets_familyCurve_joint

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.FixedSlotInterpolation
section
/-!
# Fixed slots and the path-time estimate in Section 4

Finite rows are interpolated in fixed equal-width slots. The path-time
Lipschitz constant is simplex diameter times the slot count. It does not
depend on the number of intermediate homotopy rows. This file proves the
affine estimate and literal endpoint agreement, rather than assuming a
controlled contraction for the interval carriers.
-/

namespace AbelianTargets.FixedSlots

open scoped NNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



























/-- At every interpolation row, the same slot budget controls path-time.
The number of homotopy rows does not occur in this bound. -/
theorem interpolated_row_lipschitz (T : ℕ) (hT : 0 < T)
    (row₀ row₁ : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (hedges₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (hedges₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*T) (rowPath T (fun j => mix (row₀ j) (row₁ j) r) n) := by
  apply rowPath_lipschitz T hT _ n Δ
  intro j hj
  exact mix_dist_le_of_le (hedges₀ j hj) (hedges₁ j hj) r































namespace BasedRow

variable {n : ℕ} {p q : E}









end BasedRow



















end

end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.VariableRowFamilies
section
/-! Fixed-slot row interpolation with a moving terminal vertex. -/

namespace AbelianTargets.FixedSlots

open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem rowFamily_path_time_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+1)) (fun u : unitInterval => rowFamily row₀ row₁ n (r,u)) := by
  simpa only [mul_one,Nat.cast_add,Nat.cast_one,rowFamily,Function.comp_def] using
    (interpolated_row_lipschitz (n+1) (Nat.succ_pos n) row₀ row₁ n Δ h₀ h₁ r).comp
      (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))













end
end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.RectangleHalfGluing
section
/-! Literal seam gluing of two square families, including moving endpoints. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {Z : Type*} [MetricSpace Z]







theorem halfGlue_path_time_lipschitz (F G : unitInterval × unitInterval → Z) {K : ℝ≥0}
    (hF : ∀ r, LipschitzWith K (fun u => F (r,u)))
    (hG : ∀ r, LipschitzWith K (fun u => G (r,u))) (r : unitInterval) :
    LipschitzWith K (fun u => halfGlue F G (r,u)) := by
  by_cases hr : (r : ℝ) ≤ 1/2
  · simpa only [halfGlue,halfGlueRaw,if_pos hr] using hF (clampInterval (2*(r : ℝ)))
  · simpa only [halfGlue,halfGlueRaw,if_neg hr] using hG (clampInterval (2*(r : ℝ)-1))









end
end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.FiniteIntervalGluing
section
/-! Finite families on neighboring unit intervals glue literally.
Their path-time Lipschitz constant is independent of the number of intervals. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {Z : Type*} [MetricSpace Z]



theorem intervalGlue_right (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) : intervalGlue F n ((n : ℝ)+1,u) = F n (1,u) := by
  cases n with
  | zero => simp [intervalGlue,clampInterval]
  | succ n =>
    simp only [intervalGlue]
    rw [if_neg (by push_cast; linarith)]
    have he : ((n+1 : ℕ) : ℝ)+1-((n : ℝ)+1) = 1 := by push_cast; ring
    rw [he]
    simp [clampInterval]







theorem intervalGlue_path_time_lipschitz (F : ℕ → unitInterval × unitInterval → Z)
    (n : ℕ) {K : ℝ≥0} (hF : ∀ i ≤ n, ∀ r, LipschitzWith K (fun u => F i (r,u)))
    (x : ℝ) : LipschitzWith K (fun u => intervalGlue F n (x,u)) := by
  induction n with
  | zero =>
    change LipschitzWith K (fun u => F 0 (clampInterval x,u))
    exact hF 0 le_rfl _
  | succ n ih =>
    by_cases hx : x ≤ (n : ℝ)+1
    · simpa only [intervalGlue,if_pos hx] using ih (fun i hi => hF i (by omega))
    · simpa only [intervalGlue,if_neg hx] using hF (n+1) le_rfl (clampInterval (x-((n : ℝ)+1)))









end
end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.BottomIntervalMap
section
/-! The literal affine bottom interval in barycentric carrier coordinates. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section





theorem bottomMap_on_unit (K R n : ℕ) (hn : n < R) (s : unitInterval) :
    bottomMap K R ((n : ℝ)+s) =
      FixedSlots.mix (bottomMass K R n) (bottomMass K R (n+1)) s := by
  apply FixedSlots.intervalGlue_on_unit _ (R-1) n (by omega)
  intro i hi u
  simp only [FixedSlots.mix_zero,FixedSlots.mix_one]



theorem bottomMap_zero (K R : ℕ) : bottomMap K R 0 = bottomMass K R 0 := by
  rw [bottomMap,FixedSlots.intervalGlue_zero]
  exact FixedSlots.mix_zero _ _

theorem bottomMap_right (K R : ℕ) (hR : 0 < R) : bottomMap K R R = bottomMass K R R := by
  have he : ((R-1 : ℕ) : ℝ)+1 = (R : ℝ) := by
    have hh : R-1+1=R := by omega
    exact_mod_cast hh
  unfold bottomMap
  rw [← he,FixedSlots.intervalGlue_right]
  simpa only [show R-1+1=R by omega] using FixedSlots.mix_one (bottomMass K R (R-1)) _



end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.ProbabilityTwoVertices
section
/-! Exact barycentric coordinates on an edge, used to invert the literal
height-zero carrier parametrization. -/

namespace AbelianTargets.Probability
noncomputable section
open scoped BigOperators unitInterval NNReal
variable {V : Type*} [Fintype V]















theorem weighted_unit_edge (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) (c : V → ℝ) (hstep : c w=c v+1) :
    ∑ u,p.mass u*c u=c v+p.mass w := by
  rw [p.weighted_pair_sum v w hne hp c,hstep]
  have hs := p.mass_pair_sum v w hne hp
  calc
    _ = (p.mass v+p.mass w)*c v+p.mass w := by ring
    _ = _ := by rw [hs]; ring

theorem weighted_singleton (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) (c : V → ℝ) : ∑ u,p.mass u*c u=c v := by
  classical
  rw [p.eq_dirac_of_singleton v hp]
  simp [dirac_mass]

end
end AbelianTargets.Probability

end

-- Preserved source skeleton: AbelianTargets.BottomCoordinateInverse
section
/-! The actual affine bottom interval is inverted by its barycentric
horizontal coordinate, on every singleton and unit bottom edge. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
open scoped BigOperators NNReal unitInterval







theorem bottomVertices_ne (K R n : ℕ) (hn : n < R) :
    bottomVertex K R n hn.le ≠ bottomVertex K R (n+1) (by omega) := by
  intro he
  have h := congrArg (fun v : CarrierVertex K 0 R => v.val.1) he
  dsimp [bottomVertex] at h
  omega

theorem bottomCoordinate_unit_edge (K R n : ℕ) (hn : n < R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)) :
    bottomCoordinate K R p=(n : ℝ)+p.mass (bottomVertex K R (n+1) (by omega)) := by
  exact p.weighted_unit_edge _ _ (bottomVertices_ne K R n hn) hp _
    (by simp [bottomVertex])

theorem bottomMap_inverse_unit_edge (K R n : ℕ) (hn : n < R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)) :
    bottomMap K R (bottomCoordinate K R p)=p.mass := by
  let s : unitInterval := ⟨p.mass (bottomVertex K R (n+1) (by omega)),
    p.nonneg _,p.mass_le_one _⟩
  have he := p.eq_mix_dirac_of_pair _ _ (bottomVertices_ne K R n hn) hp
  rw [bottomCoordinate_unit_edge K R n hn p hp]
  change bottomMap K R ((n : ℝ)+s)=p.mass
  rw [bottomMap_on_unit K R n hn s,bottomMass_eq K R n hn.le,
    bottomMass_eq K R (n+1) (by omega)]
  exact (congrArg Probability.mass he).symm

theorem bottomMap_at_integer (K R n : ℕ) (hn : n ≤ R) :
    bottomMap K R n=(Probability.dirac (bottomVertex K R n hn)).mass := by
  by_cases hlt : n < R
  · have h := bottomMap_on_unit K R n hlt 0
    simpa [bottomMass_eq K R n hn] using h
  · have he : n=R := by omega
    subst n
    by_cases hR : 0 < R
    · rw [bottomMap_right K R hR,bottomMass_eq K R R hn]
    · have he : R=0 := by omega
      subst R
      simpa using (bottomMap_zero K 0).trans (bottomMass_eq K 0 0 hn)

theorem bottomMap_inverse_singleton (K R n : ℕ) (hn : n ≤ R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn} : Set _)) :
    bottomMap K R (bottomCoordinate K R p)=p.mass := by
  have hc : bottomCoordinate K R p=(n : ℝ) :=
    p.weighted_singleton _ hp _
  rw [hc,bottomMap_at_integer K R n hn,p.eq_dirac_of_singleton _ hp]



theorem bottomMap_inverse (K R : ℕ) (p : Probability (CarrierVertex K 0 R))
    (hp : BottomSupported K R p) : bottomMap K R (bottomCoordinate K R p)=p.mass := by
  rcases hp with ⟨n,hn,hp⟩ | ⟨n,hn,hp⟩
  · exact bottomMap_inverse_singleton K R n hn p hp
  · exact bottomMap_inverse_unit_edge K R n hn p hp

end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.BottomEdgeSplice
section
/-! The complete moving-endpoint family across one bottom edge. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]












namespace BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)










theorem family_path_time_lipschitz (r : unitInterval) :
    LipschitzWith (Δ*(n+2)) (fun u => D.family (r,u)) := by
  apply halfGlue_path_time_lipschitz
  · intro r
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two,leftFamily] using
      rowFamily_path_time_lipschitz D.leftRow D.seamRow (n+1) Δ D.left_edges D.seam_edges r
  · exact correctedCarry_path_time_lipschitz n D.carry q _ Δ D.carry_speed
      (fun r => D.carry.target r) (fun r => by
        have h := (mix_lipschitz p q Δ D.edge_bound).dist_le_mul 1 (upperHalf r)
        rw [mix_one] at h
        exact h.trans (mul_le_of_le_one_right Δ.property (interval_dist_le_one _ _)))













end BottomSpliceData
end
end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.BottomHeightZero
section
namespace AbelianTargets.IntervalCarriers
noncomputable section

theorem CarrierFace.zero_of_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    {s : Finset Vertex} (hs : CarrierFace m K A B s) (hzero : ∀ v ∈ s,v.2=0) :
    CarrierFace m 0 A B s := by
  induction K with
  | zero => exact hs
  | succ K ih =>
    apply ih
    exact hs.lower_of_height hm (fun v hv => by rw [hzero v hv]; exact Nat.zero_le K)

theorem realization_bottomSupported_of_height_zero {m K R : ℕ} (hm : 1 ≤ m)
    (p : Realization m K 0 R) (hzero : ∀ v,0 < p.val.mass v → v.val.2=0) :
    BottomSupported K R p.val := by
  let s := p.val.positiveSupport
  have hs := (mem_simplexFaces s).mp (positiveSupport_mem p)
  apply bottomSupported_of_face p.val s (hs.zero_of_height hm ?_) p.val.supportedOn_positiveSupport
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  exact hzero w ((Probability.mem_positiveSupport p.val w).mp hw)

theorem bottomMap_inverse_height_zero {m K R : ℕ} (hm : 1 ≤ m)
    (p : Realization m K 0 R) (hzero : ∀ v,0 < p.val.mass v → v.val.2=0) :
    bottomMap K R (bottomCoordinate K R p.val)=p.val.mass :=
  bottomMap_inverse K R p.val (realization_bottomSupported_of_height_zero hm p hzero)

end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.CurveFamilyStages
section
/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section







theorem familyCurve_seam {X Y : Type*} (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (n : ℕ) (x : X) :
    familyCurve H (n+1)
      ((((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)),x)=
    H (n+1) (x,clampInterval (((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ))) := by
  have h₁ : (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))=1 := by field_simp
  have h₂ : ((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ)=0 := by field_simp; simp
  rw [h₁,h₂,clampInterval_zero,familyCurve_one,hseam]

theorem familyCurve_track {X Y : Type*} [MetricSpace Y] (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => H n (x,t)))
    (n : ℕ) (x : X) : LipschitzWith ((n : ℝ≥0)*D) (fun t : ℝ => familyCurve H n (t,x)) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [familyCurve] using (LipschitzWith.const (H 0 (x,0)) : LipschitzWith 0 (fun _ : ℝ => H 0 (x,0)))
  | one => simpa only [Nat.cast_one,one_mul,familyCurve,Function.comp_def,mul_one] using
      (htrack 0 x).comp lipschitz_clampInterval
  | more n ih ih' =>
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      rw [abs_of_nonneg (by positivity)]
    have hf := ih'.comp (lipschitz_affine_le r (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr)
    have hconst : (((n+1 : ℕ) : ℝ≥0)*D)*r=((n+2 : ℕ) : ℝ≥0)*D := by dsimp [r]; field_simp
    rw [hconst] at hf
    have hg := ((htrack (n+1) x).comp lipschitz_clampInterval).comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ) (-((n+1 : ℕ) : ℝ)) (by
        change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
        rw [abs_of_nonneg (by positivity)]))
    have hconst' : (D*1)*((n+2 : ℕ) : ℝ≥0)=((n+2 : ℕ) : ℝ≥0)*D := by ring
    rw [hconst'] at hg
    have he := lipschitz_glue_at _ _ hf hg (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (by
      simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using familyCurve_seam H hseam n x)
    simpa only [familyCurve,Function.comp_def,add_zero,sub_eq_add_neg] using he









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

theorem familyHomotopy_track {X Y : Type*} [MetricSpace Y] (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => H n (x,t))) (n : ℕ) (x : X) :
    LipschitzWith ((n : ℝ≥0)*D) (fun t : I => familyHomotopy H n (x,t)) := by
  have he : LipschitzWith 1 ((↑) : I → ℝ) := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    change dist x y ≤ (1 : ℝ)*dist x y; simp
  simpa only [familyHomotopy,Function.comp_def,mul_one] using (familyCurve_track H hseam D htrack n x).comp he

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



theorem heightDeformation_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) :
    LipschitzWith ((K : ℝ≥0)*(m+2 : ℕ)) (fun t => heightDeformation hm K A B (p,t)) :=
  familyHomotopy_track _ (heightChain hm K A B).seam _ (heightChain hm K A B).track K p









end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.DigitBottomCombing
section
/-! The actual digit combing of the entire finite bottom interval, with common slots. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section





















theorem bottomCombing_path_time_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun u => bottomCombing m hm R (x,u)) := by
  apply FixedSlots.intervalGlue_path_time_lipschitz
  intro i hi r
  rw [digitEdgeFamily_eq m hm R i (by omega)]
  simpa only [one_mul,Nat.cast_add,Nat.cast_ofNat] using
    (digitSplice m hm R i (by omega)).family_path_time_lipschitz r











end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.RealizedBottomCombing
section
/-! The logarithmic-speed bottom combing takes values in the actual carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section







theorem realizedBottomCombing_path_time_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ)
    (hR : 0 < R) (x : ℝ) : LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun u => realizedBottomCombing m hm R hR (x,u)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (realizedBottomCombing m hm R hR (x,u)).1.mass
    (realizedBottomCombing m hm R hR (x,v)).1.mass ≤ _
  rw [realizedBottomCombing_mass,realizedBottomCombing_mass]
  exact (bottomCombing_path_time_lipschitz m hm R hR x).dist_le_mul u v









end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.CarrierControlledContraction
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! An actual controlled contraction of the finite triangulated interval
carrier. Every track has logarithmic speed; the joint constant is finite. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section



theorem bottomFinish_zero (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    bottomFinish m hm R hR (p,0)=heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R (p,1) := by
  apply Subtype.ext
  apply Probability.ext
  simp only [bottomFinish,unitInterval.symm_zero,realizedBottomCombing_target_mass]
  exact bottomMap_inverse_height_zero (by omega : 1 ≤ m) _
    (heightDeformation_terminal (by omega : 1 ≤ m) p)



theorem bottomFinish_track (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    LipschitzWith (carryRowBudget m R+2 : ℝ≥0) (fun t => bottomFinish m hm R hR (p,t)) := by
  simpa only [bottomFinish,Function.comp_def,mul_one] using
    (realizedBottomCombing_path_time_lipschitz m hm R hR _).comp lipschitz_interval_symm





theorem bottomFinish_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (t : unitInterval) :
    bottomFinish m hm R hR (point (carrierBase (Nat.log m R) R),t)=point (carrierBase (Nat.log m R) R) := by
  unfold bottomFinish
  rw [heightDeformation_fixes_bottom (by omega : 1 ≤ m) _ (base_height_zero _ _)]
  have hc : bottomCoordinate (Nat.log m R) R (point (carrierBase (Nat.log m R) R) : Realization m (Nat.log m R) 0 R).1=0 := by
    classical
    simp [bottomCoordinate,Probability.weightedCoordinate,point,Probability.dirac_mass,carrierBase]
  rw [hc]
  exact realizedBottomCombing_base m hm R hR _





















end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.GeneralCarrierHeightRestriction
section
set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable









theorem restrictCarrierHeight_preserves_bottom {m K T : ℕ} {A B : ℤ}
    (hm : 1 ≤ m) (hKT : K ≤ T) (p : Realization m T A B)
    (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K)
    (hzero : ∀ v,0 < p.1.mass v → v.1.2=0) :
    ∀ v,0 < (restrictCarrierHeight hm hKT p hp).1.mass v → v.1.2=0 := by
  intro w hw
  obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexFloor (K := K)) p.1 w).mp hw
  rw [←hv]
  simp [vertexFloor,hzero v hvp]

end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.CommonHeightCarrierContraction
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Controlled contractions at a common height, including intervals shorter
than the ambient logarithmic scale. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section









theorem bottomEndpointLower_bottom (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    ∀ v,0 < (bottomEndpointLower m hm T R hlog p).1.mass v → v.1.2=0 :=
  restrictCarrierHeight_preserves_bottom hm hlog _ _ (heightDeformation_terminal hm p)

theorem bottomEndpointLower_joint (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) : ∃ J : ℝ≥0,LipschitzWith J (bottomEndpointLower m hm T R hlog) := by
  obtain ⟨J,hJ⟩ := heightDeformation_joint (K := T) (A := 0) (B := R) hm
  have he := hJ.comp ((LipschitzWith.id : LipschitzWith 1 (id : Realization m T 0 R → _)).prodMk
    (LipschitzWith.const (1 : unitInterval)))
  refine ⟨J*max 1 0,LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [←(isometry_include (m := m) (A := 0) (B := R) hlog).dist_eq,
    include_bottomEndpointLower,include_bottomEndpointLower]
  exact he.dist_le_mul p q





theorem commonHeightBottomFinish_zero (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightBottomFinish m hm T R hR hlog (p,0)=heightDeformation (by omega : 1 ≤ m) T 0 R (p,1) := by
  unfold commonHeightBottomFinish
  rw [bottomFinish_zero,heightDeformation_fixes_bottom (by omega : 1 ≤ m) _
    (bottomEndpointLower_bottom m (by omega : 1 ≤ m) T R hlog p),include_bottomEndpointLower]



theorem commonHeightBottomFinish_track (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun t => commonHeightBottomFinish m hm T R hR hlog (p,t)) := by
  simpa only [commonHeightBottomFinish,Function.comp_def,one_mul] using
    (isometry_include (m := m) (A := 0) (B := R) hlog).lipschitz.comp
      (bottomFinish_track m hm R hR (bottomEndpointLower m (by omega : 1 ≤ m) T R hlog p))

theorem commonHeightBottomFinish_joint (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) :
    ∃ J : ℝ≥0,LipschitzWith J (commonHeightBottomFinish m hm T R hR hlog) := by
  obtain ⟨Jr,hJr⟩ := bottomEndpointLower_joint m (by omega : 1 ≤ m) T R hlog
  obtain ⟨Jb,hJb⟩ := bottomFinish_joint m hm R hR
  have hp := (hJr.comp LipschitzWith.prod_fst).prodMk
    (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : Realization m T 0 R × unitInterval → unitInterval))
  refine ⟨Jb*max (Jr*1) 1,?_⟩
  simpa only [commonHeightBottomFinish,Function.comp_def,one_mul] using
    (isometry_include (m := m) (A := 0) (B := R) hlog).lipschitz.comp (hJb.comp hp)

theorem commonHeightBottomFinish_base (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (t : unitInterval) :
    commonHeightBottomFinish m hm T R hR hlog (point (carrierBase T R),t)=point (carrierBase T R) := by
  simp [commonHeightBottomFinish,bottomFinish_base]



theorem commonHeightStages_seam (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (n : ℕ) (p : Realization m T 0 R) :
    commonHeightStages m hm T R hR hlog n (p,1)=commonHeightStages m hm T R hR hlog (n+1) (p,0) := by
  cases n with
  | zero => exact (commonHeightBottomFinish_zero m hm T R hR hlog p).symm
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_one m hm T R hR hlog p
    | succ n => rfl





theorem commonHeightContractionMap_track (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    LipschitzWith (commonHeightSpeed m T R) (fun t => commonHeightContractionMap m hm T R hR hlog (p,t)) := by
  apply familyHomotopy_track _ (commonHeightStages_seam m hm T R hR hlog)
    (max ((T : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)) _ 2 p
  intro n q
  cases n with
  | zero => exact (heightDeformation_track (by omega : 1 ≤ m) q).weaken (le_max_left _ _)
  | succ n =>
    cases n with
    | zero => exact (commonHeightBottomFinish_track m hm T R hR hlog q).weaken (le_max_right _ _)
    | succ n => exact (LipschitzWith.const _).weaken (by positivity)

theorem commonHeightContractionMap_joint (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) : ∃ J : ℝ≥0,LipschitzWith J (commonHeightContractionMap m hm T R hR hlog) := by
  apply familyHomotopy_joint _ (commonHeightStages_seam m hm T R hR hlog) _ 2
  intro n
  cases n with
  | zero => exact heightDeformation_joint (by omega : 1 ≤ m)
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_joint m hm T R hR hlog
    | succ n => exact ⟨0,LipschitzWith.const _⟩





theorem commonHeightContractionMap_base (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (t : unitInterval) :
    commonHeightContractionMap m hm T R hR hlog (point (carrierBase T R),t)=point (carrierBase T R) := by
  apply familyCurve_fixed
  intro n u
  cases n with
  | zero => exact heightDeformation_fixes_bottom (by omega : 1 ≤ m) _ (base_height_zero _ _) u
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_base m hm T R hR hlog u
    | succ n => rfl

theorem exists_commonHeightControlledContraction (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) :
    ∃ J : ℝ≥0,Nonempty (ControlledContraction
      (point (carrierBase T R) : Realization m T 0 R) (commonHeightSpeed m T R) J) := by
  obtain ⟨J,hJ⟩ := commonHeightContractionMap_joint m hm T R hR hlog
  refine ⟨J,⟨{
    map := commonHeightContractionMap m hm T R hR hlog
    continuous := hJ.continuous
    at_zero := commonHeightContractionMap_zero m hm T R hR hlog
    at_one := commonHeightContractionMap_one m hm T R hR hlog
    fixes := commonHeightContractionMap_base m hm T R hR hlog
    track := commonHeightContractionMap_track m hm T R hR hlog
    joint := hJ }⟩⟩

end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.UniformCarrierContraction
section
set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.ControlledContraction
open scoped NNReal
noncomputable section



end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped NNReal BigOperators
noncomputable section



theorem commonHeightSpeed_le_uniform (m T R : ℕ) (hlog : Nat.log m R ≤ T) :
    commonHeightSpeed m T R ≤ uniformCarrierSpeed m T := by
  have h₀ : T*(m+2)≤(3*m+8)*(T+1) := by nlinarith
  have h₁ : carryRowBudget m R+2≤(3*m+8)*(T+1) := by
    dsimp [carryRowBudget]
    nlinarith
  unfold commonHeightSpeed uniformCarrierSpeed
  have ht : (T : ℝ≥0)*(m+2 : ℕ) ≤ ((3*m+8)*(T+1) : ℕ) := by exact_mod_cast h₀
  have hb : (carryRowBudget m R+2 : ℝ≥0) ≤ ((3*m+8)*(T+1) : ℕ) := by exact_mod_cast h₁
  calc
    _ ≤ 2*(((3*m+8)*(T+1) : ℕ) : ℝ≥0) := mul_le_mul_left' (max_le ht hb) 2
    _ = ((2*((3*m+8)*(T+1)) : ℕ) : ℝ≥0) := by norm_cast





end
end AbelianTargets.IntervalCarriers

end

set_option backward.isDefEq.respectTransparency false
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers
open scoped NNReal BigOperators

theorem solution (m : ℕ) (hm : 2 ≤ m) (T S : ℕ)
    (hST : Nat.log m S ≤ T) :
    ∃ J : ℝ≥0,∀ R : ℕ,∀ hR : 0 < R,R ≤ S →
      Nonempty (ControlledContraction
        (point (carrierBase T R) : Realization m T 0 R) (uniformCarrierSpeed m T) J) := by
  classical
  let Q (r : Fin (S+1)) (hr : 0 < r.val) :=
    exists_commonHeightControlledContraction m hm T r.val hr
      ((Nat.log_mono_right (by omega : r.val ≤ S)).trans hST)
  let j : Fin (S+1) → ℝ≥0 := fun r => if hr : 0 < r.val then (Q r hr).choose else 0
  refine ⟨∑ r,j r,?_⟩
  intro R hR hRS
  let r : Fin (S+1) := ⟨R,by omega⟩
  obtain ⟨C⟩ := (Q r hR).choose_spec
  have hj : (Q r hR).choose ≤ ∑ a,j a := by
    have hs : j r ≤ ∑ a,j a := Finset.single_le_sum (fun a _ => by positivity) (Finset.mem_univ r)
    have he : j r=(Q r hR).choose := by unfold j; rw [dif_pos hR]
    rw [he] at hs
    exact hs
  exact ⟨C.weaken (uniformCarrierSpeed m T) (∑ a,j a)
    (commonHeightSpeed_le_uniform m T R ((Nat.log_mono_right hRS).trans hST)) hj⟩
