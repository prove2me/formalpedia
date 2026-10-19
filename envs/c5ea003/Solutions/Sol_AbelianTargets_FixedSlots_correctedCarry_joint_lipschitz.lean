-- Prove2me | solution 1 for AbelianTargets.FixedSlots.correctedCarry_joint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:01:36.507574+00:00
-- url     : https://prove2.me/submissions/aaf9de1f-0126-4ff3-8ba4-c6ba98a264ac

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointHomotopyGluing
import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.EndpointCorrection
section
/-! Reserving the final path slot for a continuously moving endpoint. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]











theorem lipschitz_clamp_affine (c : ℝ≥0) (b : ℝ) :
    LipschitzWith c (fun u : ℝ => clampInterval ((c : ℝ)*u+b)) := by
  simpa only [one_mul,Function.comp_def] using
    lipschitz_clampInterval.comp (lipschitz_affine_le c c b (by simp))















end
end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.JointEndpointCorrection
section
/-! Finite joint Lipschitz constants for the reserved endpoint slot. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mix_edge_family_lipschitz (q : E) (e : unitInterval → E) (C Δ : ℝ≥0)
    (he : LipschitzWith C e) (hq : ∀ r, dist q (e r) ≤ Δ) :
    LipschitzWith (C+Δ) (fun z : unitInterval × unitInterval => mix q (e z.1) z.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨r,u⟩ ⟨s,v⟩
  have hu := (mix_lipschitz q (e r) Δ (hq r)).dist_le_mul u v
  have hs : dist (mix q (e r) v) (mix q (e s) v) ≤ C*dist r s := by
    calc
      _ ≤ (1-(v : ℝ))*dist q q+(v : ℝ)*dist (e r) (e s) := mix_dist_le _ _ _ _ v
      _ ≤ dist (e r) (e s) := by
        simp only [dist_self,mul_zero,zero_add]
        exact mul_le_of_le_one_left dist_nonneg v.property.2
      _ ≤ _ := he.dist_le_mul r s
  calc
    _ ≤ dist (mix q (e r) u) (mix q (e r) v)+dist (mix q (e r) v) (mix q (e s) v) :=
      dist_triangle _ _ _
    _ ≤ Δ*dist u v+C*dist r s := add_le_add hu hs
    _ ≤ Δ*dist (r,u) (s,v)+C*dist (r,u) (s,v) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) Δ.property)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) C.property)
    _ = (C+Δ : ℝ≥0)*dist (r,u) (s,v) := by simp [add_mul]; ring

theorem lipschitz_id_clamp_affine (c : ℝ≥0) (b : ℝ) :
    LipschitzWith (max 1 c) (fun z : unitInterval × ℝ =>
      (z.1,clampInterval ((c : ℝ)*z.2+b))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change max (dist x.1 y.1) (dist (clampInterval ((c : ℝ)*x.2+b))
    (clampInterval ((c : ℝ)*y.2+b))) ≤ _
  apply max_le
  · calc
      _ ≤ dist x y := le_max_left _ _
      _ ≤ (max 1 c : ℝ≥0)*dist x y := by
        have h : (1 : ℝ) ≤ (max 1 c : ℝ≥0) := by exact_mod_cast le_max_left 1 c
        nlinarith [dist_nonneg (x := x) (y := y)]
  · calc
      _ ≤ c*dist x.2 y.2 := (lipschitz_clamp_affine c b).dist_le_mul _ _
      _ ≤ (max 1 c : ℝ≥0)*dist x y := by
        exact mul_le_mul
          (by exact_mod_cast le_max_right 1 c) (le_max_right _ _)
          dist_nonneg (by positivity)

theorem lipschitz_glue_product_snd {Z : Type*} [PseudoMetricSpace Z]
    {K : ℝ≥0} (f g : unitInterval × ℝ → Z) (hf : LipschitzWith K f)
    (hg : LipschitzWith K g) (c : ℝ) (hmatch : ∀ r, f (r,c) = g (r,c)) :
    LipschitzWith (2*K) (fun z => if z.2 ≤ c then f z else g z) := by
  have hswap : LipschitzWith 1 (fun z : unitInterval × ℝ => (z.2,z.1)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change max (dist x.2 y.2) (dist x.1 y.1) ≤ (1 : ℝ)*max (dist x.1 y.1) (dist x.2 y.2)
    rw [one_mul,max_comm]
  have hswap' : LipschitzWith 1 (fun z : ℝ × unitInterval => (z.2,z.1)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change max (dist x.2 y.2) (dist x.1 y.1) ≤ (1 : ℝ)*max (dist x.1 y.1) (dist x.2 y.2)
    rw [one_mul,max_comm]
  have hh := lipschitz_glue_product_at (fun z : ℝ × unitInterval => f (z.2,z.1))
    (fun z : ℝ × unitInterval => g (z.2,z.1))
    (by simpa only [mul_one] using hf.comp hswap')
    (by simpa only [mul_one] using hg.comp hswap') c hmatch
  simpa only [Function.comp_def,mul_one] using hh.comp hswap



end
end AbelianTargets.FixedSlots

end

/-! Finite joint Lipschitz constants for the reserved endpoint slot. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) {J C Δ : ℝ≥0}
    (hF : LipschitzWith J F) (htarget : ∀ r, F (r,1) = q)
    (he : LipschitzWith C e) (hq : ∀ r, dist q (e r) ≤ Δ) :
    ∃ L : ℝ≥0, LipschitzWith L (correctedCarry n F q e) := by
  let K := max (J*max 1 (correctionScale n)) ((C+Δ)*max 1 ((n : ℝ≥0)+2))
  have h₀ : LipschitzWith K (fun z : unitInterval × ℝ =>
      F (z.1,clampInterval ((correctionScale n : ℝ)*z.2))) := by
    simpa only [Function.comp_def,add_zero] using
      (hF.comp (lipschitz_id_clamp_affine (correctionScale n) 0)).weaken
        (show J*max 1 (correctionScale n) ≤ K from le_max_left _ _)
  have h₁ : LipschitzWith K (fun z : unitInterval × ℝ =>
      mix q (e z.1) (clampInterval (((n : ℝ)+2)*z.2-((n : ℝ)+1)))) := by
    have hh := (mix_edge_family_lipschitz q e C Δ he hq).comp
      (lipschitz_id_clamp_affine (n+2) (-((n : ℝ)+1)))
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,sub_eq_add_neg] using
      hh.weaken (show (C+Δ)*max 1 ((n : ℝ≥0)+2) ≤ K from le_max_right _ _)
  have hh := lipschitz_glue_product_snd _ _ h₀ h₁ (correctionCut n) (by
    intro r
    rw [correctionScale_cut,correction_final_zero]
    simp [clampInterval,htarget])
  have hi : LipschitzWith 1 (fun z : unitInterval × unitInterval => (z.1,(z.2 : ℝ))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist x y ≤ (1 : ℝ)*dist x y
    simp
  exact ⟨2*K,by simpa only [Function.comp_def,mul_one,correctedCarry,correctedCarryRaw]
    using hh.comp hi⟩
