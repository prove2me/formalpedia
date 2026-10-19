-- Prove2me | Definitions.Def_AT260939824_ControlledCone
-- name    : AT260939824_ControlledCone
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:51:34.538731+00:00
-- url     : https://prove2.me/theorems/c35d77dd-a8e0-44aa-838b-9034ce1b4c77
-- title:
--   Endpoint-preserving cone extension data
-- statement:
--   For a real normed space $E$, write
--
--   $$ B_E=\{x:\|x\|\le1\},\qquad S_E=\{x:\|x\|=1\}. $$
--
--   Boundary data are a family of paths from $p$ to $q$ in a metric target with a controlled contraction, with explicit longitudinal and transverse Lipschitz bounds. The cone-value construction extends this family to $B_E$, preserving its boundary values and endpoints. For each point of the ball it gives an actual continuous path from $p$ to $q$, equal to the prescribed path on the sphere. Its accompanying constants retain the quantitative dependence needed for rectangular extensions.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ControlledCone.lean, selected declaration lines 27-28, 30-32, 34-37, 39-73, 75, 77-90, 92-96, 98-101, 103-106, 113-119, 121-124, 126-133, 135-143, 145-154, 156-157, 159-192, 194-225, 227-241, 243-259, 261-263, 265-270, 272-277, 279-286, 288-292; SHA-256 3c3e4995830f4216b61d6b255de30d3f2c41826a24b7c4d81758a6c060460cb4. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathComparison
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Controlled radial extension of a boundary path family

The local extension step used in Lemma 5.2. The transverse rectangle is
represented by the unit ball for its scaled maximum norm. On its outer
half we use the actual relative homotopy of Lemma 5.1; on its inner half
we use the common contraction path. The construction preserves the
boundary parametrization and controls the path coordinate independently
of the joint Lipschitz constant of the contraction.

The rectangular atlas and the existence of its finite carrier
contractions are separate inputs, not conclusions of this module.
-/

namespace AbelianTargets

open scoped unitInterval NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev ConeBall (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ ≤ 1}
abbrev ConeSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

def radialDirection (x : E) (hx : 0 < ‖x‖) : ConeSphere E :=
  ⟨‖x‖⁻¹ • x, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ (ne_of_gt hx)]⟩

@[simp] theorem radialDirection_of_sphere (x : ConeSphere E) :
    radialDirection x.val (by rw [x.property]; norm_num) = x := by
  apply Subtype.ext
  simp [radialDirection, x.property]

/-- Radial projection has constant four on the outer half of a norm ball.
This applies in particular to the scaled maximum norm of a rectangle. -/
theorem radialDirection_dist_le (x y : E) (hx : (1/2 : ℝ) ≤ ‖x‖)
    (hy : (1/2 : ℝ) ≤ ‖y‖) :
    dist (radialDirection x (by linarith)) (radialDirection y (by linarith)) ≤
      4 * dist x y := by
  have ha : 0 < ‖x‖ := by linarith
  have hb : 0 < ‖y‖ := by linarith
  have hn : |‖y‖-‖x‖| ≤ dist x y := by
    simpa only [Real.dist_eq, abs_sub_comm, dist_eq_norm] using dist_norm_norm_le x y
  have hdiv : dist x y / ‖x‖ ≤ 2 * dist x y := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [show 0 ≤ dist x y from dist_nonneg]
  have hdir : ‖(radialDirection y hb).val‖ = 1 := (radialDirection y hb).property
  have hscale : ‖x‖⁻¹ • y = (‖y‖/‖x‖) • (radialDirection y hb).val := by
    simp only [radialDirection, smul_smul]
    congr 1
    field_simp
  have hdist : dist (‖x‖⁻¹ • y) (‖y‖⁻¹ • y) = |‖y‖-‖x‖| / ‖x‖ := by
    rw [hscale]
    change dist ((‖y‖/‖x‖) • (radialDirection y hb).val)
      (radialDirection y hb).val = _
    have heq : (‖y‖/‖x‖) • (radialDirection y hb).val - (radialDirection y hb).val =
        (‖y‖/‖x‖-1) • (radialDirection y hb).val := by rw [sub_smul,one_smul]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, hdir, mul_one]
    rw [div_sub_one (ne_of_gt ha), abs_div, abs_of_pos ha]
  change dist (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) ≤ _
  calc
    _ ≤ dist (‖x‖⁻¹ • x) (‖x‖⁻¹ • y) + dist (‖x‖⁻¹ • y) (‖y‖⁻¹ • y) := dist_triangle _ _ _
    _ = dist x y / ‖x‖ + |‖y‖-‖x‖| / ‖x‖ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), hdist]
      ring
    _ ≤ dist x y / ‖x‖ + dist x y / ‖x‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hn (le_of_lt ha))
    _ ≤ 4 * dist x y := by linarith

def coneParameter (x : ConeBall E) : I := clampInterval (2*(1-‖x.val‖))

omit [NormedSpace ℝ E] in
theorem coneParameter_lipschitz : LipschitzWith 2 (coneParameter (E := E)) := by
  have hn : LipschitzWith 1 (fun x : ConeBall E => ‖x.val‖) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq,dist_eq_norm] using dist_norm_norm_le x.val y.val
  have ha := (lipschitz_affine_le 2 (-2) 2 (by norm_num)).comp hn
  have hh := lipschitz_clampInterval.comp ha
  have heq : (fun x : ConeBall E => clampInterval (-2*‖x.val‖+2)) = coneParameter := by
    funext x
    unfold coneParameter
    congr 1
    ring
  simpa only [Function.comp_def, mul_one,one_mul,heq] using hh

omit [NormedSpace ℝ E] in
theorem coneParameter_outer (x : ConeBall E) (hx : (1/2 : ℝ) ≤ ‖x.val‖) :
    (coneParameter x : ℝ) = 2*(1-‖x.val‖) := by
  have ht : 2*(1-‖x.val‖) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [x.property], by linarith⟩
  exact congrArg Subtype.val (clampInterval_coe ⟨_,ht⟩)

omit [NormedSpace ℝ E] in
@[simp] theorem coneParameter_sphere (x : ConeSphere E) :
    coneParameter (⟨x.val,by rw [x.property]⟩ : ConeBall E) = 0 := by
  simp [coneParameter, x.property]

omit [NormedSpace ℝ E] in
theorem coneParameter_inner (x : ConeBall E) (hx : ‖x.val‖ ≤ (1/2 : ℝ)) :
    coneParameter x = 1 := by
  exact clampInterval_of_one_le (by linarith)

namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S B : ℝ≥0}
variable (H : ControlledContraction p D J)

/-- Boundary paths are supplied with their literal parametrizations.
The hypothesis on their uniform distance is a transverse Lipschitz
bound, rather than a path homotopy or existence assumption. -/
structure BoundaryPathFamily (p q : Z) (S B : ℝ≥0) where
  path : ConeSphere E → Path p q
  path_lipschitz : ∀ x, LipschitzWith S (path x)
  transverse : LipschitzWith B (fun x => (path x).toContinuousMap)

def coneValue (F : BoundaryPathFamily (E := E) p q S B) (x : ConeBall E) (u : I) : Z :=
  if hx : (1/2 : ℝ) ≤ ‖x.val‖ then
    H.relativeHomotopy (F.path (radialDirection x.val (by linarith))) (coneParameter x,u)
  else H.shortPath q u

theorem coneValue_inner (F : BoundaryPathFamily (E := E) p q S B)
    (x : ConeBall E) (hx : ‖x.val‖ ≤ (1/2 : ℝ)) (u : I) :
    H.coneValue F x u = H.shortPath q u := by
  unfold coneValue
  split_ifs with h
  · rw [coneParameter_inner x hx]
    exact (H.relativeHomotopy _).map_one_left u
  · rfl

/-- The prescribed boundary path is retained exactly, including its
parametrization. -/
theorem coneValue_boundary (F : BoundaryPathFamily (E := E) p q S B)
    (x : ConeSphere E) (u : I) :
    H.coneValue F ⟨x.val,by rw [x.property]⟩ u = F.path x u := by
  unfold coneValue
  rw [dif_pos (by rw [x.property]; norm_num), coneParameter_sphere]
  rw [radialDirection_of_sphere]
  exact (H.relativeHomotopy _).map_zero_left u

theorem coneValue_path_lipschitz (F : BoundaryPathFamily (E := E) p q S B)
    (x : ConeBall E) : LipschitzWith (3*max S D) (H.coneValue F x) := by
  unfold coneValue
  split_ifs
  · exact H.relativeHomotopy_lipschitz _ (F.path_lipschitz _) _
  · exact (H.shortPath_lipschitz q).weaken (by
      calc D ≤ max S D := le_max_right _ _
           _ ≤ 3*max S D := by
             simpa only [one_mul] using mul_le_mul_of_nonneg_right
               (show (1 : ℝ≥0) ≤ 3 by norm_num) (show 0 ≤ max S D from bot_le))

def coneTransverseConstant (S D J B : ℝ≥0) : ℝ≥0 :=
  24*(1+J)*(4*B+2*(S+D))

theorem coneValue_outer_dist_le (F : BoundaryPathFamily (E := E) p q S B)
    (x y : ConeBall E) (hx : (1/2 : ℝ) ≤ ‖x.val‖) (hy : (1/2 : ℝ) ≤ ‖y.val‖)
    (u : I) :
    dist (H.coneValue F x u) (H.coneValue F y u) ≤
      (coneTransverseConstant S D J B : ℝ) * dist x y := by
  let a := radialDirection x.val (by linarith : 0 < ‖x.val‖)
  let b := radialDirection y.val (by linarith : 0 < ‖y.val‖)
  have hπ : dist a b ≤ 4*dist x y := radialDirection_dist_le x.val y.val hx hy
  have hP := F.transverse.dist_le_mul a b
  have hs := coneParameter_lipschitz.dist_le_mul x y
  have hR := H.relativeHomotopy_uniform_comparison (F.path a) (F.path b)
    (F.path_lipschitz a) (coneParameter x) (coneParameter y)
  have hp := ContinuousMap.dist_apply_le_dist u
    (f := ((H.relativeHomotopy (F.path a)).eval (coneParameter x)).toContinuousMap)
    (g := ((H.relativeHomotopy (F.path b)).eval (coneParameter y)).toContinuousMap)
  rw [coneValue,dif_pos hx,coneValue,dif_pos hy]
  change dist (H.relativeHomotopy (F.path a) (coneParameter x,u))
    (H.relativeHomotopy (F.path b) (coneParameter y,u)) ≤ _
  have hinput : dist (F.path a).toContinuousMap (F.path b).toContinuousMap ≤
      4*(B : ℝ)*dist x y := by
    calc _ ≤ (B : ℝ)*dist a b := hP
         _ ≤ (B : ℝ)*(4*dist x y) := mul_le_mul_of_nonneg_left hπ B.property
         _ = _ := by ring
  have hparam : dist (coneParameter x) (coneParameter y) ≤ 2*dist x y := hs
  calc
    _ ≤ dist ((H.relativeHomotopy (F.path a)).eval (coneParameter x)).toContinuousMap
      ((H.relativeHomotopy (F.path b)).eval (coneParameter y)).toContinuousMap := hp
    _ ≤ 24*(1+(J : ℝ))*(dist (F.path a).toContinuousMap (F.path b).toContinuousMap+
      ((S : ℝ)+D)*dist (coneParameter x) (coneParameter y)) := hR
    _ ≤ 24*(1+(J : ℝ))*(4*(B : ℝ)*dist x y+((S : ℝ)+D)*(2*dist x y)) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hinput (mul_le_mul_of_nonneg_left hparam (by positivity))
      · positivity
    _ = _ := by simp only [coneTransverseConstant,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat,NNReal.coe_one]; ring

theorem coneValue_outer_inner_dist_le (F : BoundaryPathFamily (E := E) p q S B)
    (x y : ConeBall E) (hx : (1/2 : ℝ) ≤ ‖x.val‖) (hy : ‖y.val‖ ≤ (1/2 : ℝ))
    (u : I) :
    dist (H.coneValue F x u) (H.coneValue F y u) ≤
      (coneTransverseConstant S D J B : ℝ) * dist x y := by
  let a := radialDirection x.val (by linarith : 0 < ‖x.val‖)
  have hnorm : |‖x.val‖-‖y.val‖| ≤ dist x y := by
    simpa only [Real.dist_eq,Subtype.dist_eq,dist_eq_norm] using dist_norm_norm_le x.val y.val
  have ht : dist (coneParameter x) (1 : I) ≤ 2*dist x y := by
    rw [Subtype.dist_eq,Real.dist_eq,Set.Icc.coe_one,coneParameter_outer x hx]
    rw [abs_of_nonpos (by linarith [x.property])]
    rw [abs_of_nonneg (by linarith)] at hnorm
    linarith
  have hR := (H.relativeHomotopy_parameter_lipschitz (F.path a) (F.path_lipschitz a) u).dist_le_mul
    (coneParameter x) 1
  rw [coneValue,dif_pos hx,H.coneValue_inner F y hy]
  change dist (H.relativeHomotopy (F.path a) (coneParameter x,u)) (H.shortPath q u) ≤ _
  have hend := (H.relativeHomotopy (F.path a)).map_one_left u
  change H.relativeHomotopy (F.path a) (1,u) = H.shortPath q u at hend
  rw [← hend]
  simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat,NNReal.coe_one] at hR
  calc
    _ ≤ 24*(1+(J : ℝ))*((S : ℝ)+D)*dist (coneParameter x) 1 := hR
    _ ≤ 24*(1+(J : ℝ))*((S : ℝ)+D)*(2*dist x y) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (coneTransverseConstant S D J B : ℝ)*dist x y := by
      simp only [coneTransverseConstant,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat,NNReal.coe_one]
      calc
        _ = 24*(1+(J : ℝ))*(2*((S : ℝ)+D))*dist x y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity : 0 ≤ 4*(B : ℝ)))
            (by positivity : 0 ≤ 24*(1+(J : ℝ)))) dist_nonneg

/-- A uniform transverse bound on the complete cone, including the
interface with the constant inner half. -/
theorem coneValue_transverse_lipschitz (F : BoundaryPathFamily (E := E) p q S B)
    (u : I) : LipschitzWith (coneTransverseConstant S D J B) (fun x => H.coneValue F x u) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  by_cases hx : (1/2 : ℝ) ≤ ‖x.val‖
  · by_cases hy : (1/2 : ℝ) ≤ ‖y.val‖
    · exact H.coneValue_outer_dist_le F x y hx hy u
    · exact H.coneValue_outer_inner_dist_le F x y hx (le_of_not_ge hy) u
  · by_cases hy : (1/2 : ℝ) ≤ ‖y.val‖
    · rw [dist_comm (H.coneValue F x u),dist_comm x y]
      exact H.coneValue_outer_inner_dist_le F y x hy (le_of_not_ge hx) u
    · rw [H.coneValue_inner F x (le_of_not_ge hx),H.coneValue_inner F y (le_of_not_ge hy),dist_self]
      positivity

theorem coneValue_joint_lipschitz (F : BoundaryPathFamily (E := E) p q S B) :
    LipschitzWith (coneTransverseConstant S D J B+3*max S D)
      (fun z : ConeBall E × I => H.coneValue F z.1 z.2) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  have hx := (H.coneValue_transverse_lipschitz F x.2).dist_le_mul x.1 y.1
  have hu := (H.coneValue_path_lipschitz F y.1).dist_le_mul x.2 y.2
  have h₁ : dist x.1 y.1 ≤ dist x y := by simp only [Prod.dist_eq]; exact le_max_left _ _
  have h₂ : dist x.2 y.2 ≤ dist x y := by simp only [Prod.dist_eq]; exact le_max_right _ _
  calc
    _ ≤ dist (H.coneValue F x.1 x.2) (H.coneValue F y.1 x.2)+
      dist (H.coneValue F y.1 x.2) (H.coneValue F y.1 y.2) := dist_triangle _ _ _
    _ ≤ (coneTransverseConstant S D J B : ℝ)*dist x.1 y.1+(3*max S D : ℝ≥0)*dist x.2 y.2 := add_le_add hx hu
    _ ≤ (coneTransverseConstant S D J B : ℝ)*dist x y+(3*max S D : ℝ≥0)*dist x y :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (coneTransverseConstant S D J B).property)
        (mul_le_mul_of_nonneg_left h₂ (3*max S D).property)
    _ = _ := by simp only [NNReal.coe_add]; ring

theorem continuous_coneValue (F : BoundaryPathFamily (E := E) p q S B) :
    Continuous (fun z : ConeBall E × I => H.coneValue F z.1 z.2) :=
  (H.coneValue_joint_lipschitz F).continuous

@[simp] theorem coneValue_source (F : BoundaryPathFamily (E := E) p q S B) (x : ConeBall E) :
    H.coneValue F x 0 = p := by
  unfold coneValue
  split_ifs
  · exact ((H.relativeHomotopy _).eval _).source
  · exact (H.shortPath q).source

@[simp] theorem coneValue_target (F : BoundaryPathFamily (E := E) p q S B) (x : ConeBall E) :
    H.coneValue F x 1 = q := by
  unfold coneValue
  split_ifs
  · exact ((H.relativeHomotopy _).eval _).target
  · exact (H.shortPath q).target

/-- A genuine continuous path family filling the boundary family.
Together with the preceding bounds this is the local coning step of
Lemma 5.2; no CW decomposition or carrier is assumed to exist here. -/
def conePath (F : BoundaryPathFamily (E := E) p q S B) (x : ConeBall E) : Path p q where
  toFun := H.coneValue F x
  continuous_toFun := (H.coneValue_path_lipschitz F x).continuous
  source' := H.coneValue_source F x
  target' := H.coneValue_target F x

@[simp] theorem conePath_boundary (F : BoundaryPathFamily (E := E) p q S B) (x : ConeSphere E) :
    H.conePath F ⟨x.val,by rw [x.property]⟩ = F.path x := by
  apply Path.ext
  funext u
  exact H.coneValue_boundary F x u





end ControlledContraction
end
end AbelianTargets


