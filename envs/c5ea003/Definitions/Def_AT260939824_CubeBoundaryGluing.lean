-- Prove2me | Definitions.Def_AT260939824_CubeBoundaryGluing
-- name    : AT260939824_CubeBoundaryGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:52:31.153613+00:00
-- url     : https://prove2.me/theorems/773ac135-2194-4248-98af-5032c25b3f1d
-- title:
--   Lipschitz bounds from the faces of a cube
-- statement:
--   Let $\iota$ be a finite coordinate type, and equip $\mathbb R^\iota$ with the maximum norm. For nonnegative constants $B,D$ and a map $f$ on its unit sphere, suppose the image has diameter at most $D$ and its restriction to each coordinate face has Lipschitz constant $B$. Then
--
--   $$ \operatorname{Lip}(f)\le2B+D. $$
--
--   The coordinate and extreme-coordinate interfaces identify this sphere with the cube boundary. This gives a global estimate from face estimates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CubeBoundaryGluing.lean, selected declaration lines 19-22, 24-32, 34-102; SHA-256 ec2ade5a4576489d45cfaf139580c19a0ca455fcbfd7a3b0e8ebf983b3a9c31c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Analysis.Normed.Group.Constructions
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
# Quantitative gluing on the boundary of a maximum-norm cube

Facewise ambient estimates imply a global boundary estimate. Points on
different nonopposite faces are joined through an actual common-face point.
Opposite faces are separated by distance two, so an image diameter bound
handles them. This includes the disconnected boundary in dimension one.
-/

namespace AbelianTargets

open scoped NNReal

noncomputable section

theorem coneSphere_coordinate_bound {ι : Type*} [Fintype ι] (x : ConeSphere (ι → ℝ)) (i : ι) :
    |x.1 i| ≤ 1 := by
  have h := norm_le_pi_norm x.1 i
  simpa only [Real.norm_eq_abs,x.2] using h

theorem coneSphere_exists_extreme {ι : Type*} [Fintype ι] (x : ConeSphere (ι → ℝ)) :
    ∃ i, |x.1 i| = 1 := by
  by_contra h
  have hne : ∀ i, |x.1 i| ≠ 1 := by simpa only [not_exists] using h
  have hlt : ‖x.1‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ)<1)).2 (fun i => by
    rw [Real.norm_eq_abs]
    exact lt_of_le_of_ne (coneSphere_coordinate_bound x i) (hne i))
  rw [x.2] at hlt
  exact (lt_irrefl _ hlt)

theorem lipschitz_cubeBoundary_of_faces {ι : Type*} [Fintype ι] {Z : Type*} [PseudoMetricSpace Z]
    (f : ConeSphere (ι → ℝ) → Z) (B C : ℝ≥0)
    (hdiam : ∀ x y, dist (f x) (f y) ≤ C)
    (hface : ∀ i (x y : ConeSphere (ι → ℝ)), |x.1 i|=1 → x.1 i=y.1 i →
      dist (f x) (f y) ≤ B*dist x y) : LipschitzWith (2*B+C) f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨i,hi⟩ := coneSphere_exists_extreme x
  obtain ⟨j,hj⟩ := coneSphere_exists_extreme y
  by_cases hij : i=j
  · subst j
    by_cases he : x.1 i=y.1 i
    · have h := hface i x y hi he
      have hb : 0 ≤ (B : ℝ)*dist x y := mul_nonneg B.2 dist_nonneg
      have hc : 0 ≤ (C : ℝ)*dist x y := mul_nonneg C.2 dist_nonneg
      simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
      linarith
    · have hxi : x.1 i=1 ∨ x.1 i= -1 := abs_eq_abs.mp (by simpa using hi)
      have hyi : y.1 i=1 ∨ y.1 i= -1 := abs_eq_abs.mp (by simpa using hj)
      have hd : 2 ≤ dist x y := by
        have hd' : |x.1 i-y.1 i| ≤ dist x y := dist_le_pi_dist x.1 y.1 i
        rcases hxi with hxi | hxi <;> rcases hyi with hyi | hyi
        · exact False.elim (he (hxi.trans hyi.symm))
        · norm_num [hxi,hyi] at hd' ⊢; exact hd'
        · norm_num [hxi,hyi] at hd' ⊢; exact hd'
        · exact False.elim (he (hxi.trans hyi.symm))
      have hdC : (C : ℝ) ≤ (C : ℝ)*dist x y := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ)≤dist x y) C.2
      have hB : 0 ≤ (2*(B : ℝ))*dist x y := by positivity
      have h := hdiam x y
      simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
      linarith
  · let w₀ : ι → ℝ := Function.update x.1 j (y.1 j)
    have hw₀ : ‖w₀‖=1 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1)).2
        intro k
        by_cases hk : k=j
        · subst k; simpa [w₀] using coneSphere_coordinate_bound y j
        · simpa [w₀,Function.update_of_ne hk,Real.norm_eq_abs] using coneSphere_coordinate_bound x k
      · have hh := norm_le_pi_norm w₀ i
        simpa [w₀,Function.update_of_ne hij,Real.norm_eq_abs,hi] using hh
    let w : ConeSphere (ι → ℝ) := ⟨w₀,hw₀⟩
    have hxw : dist x w ≤ dist x y := by
      change dist x.1 w₀ ≤ dist x.1 y.1
      apply (dist_pi_le_iff (dist_nonneg : 0≤dist x.1 y.1)).2
      intro k
      by_cases hk : k=j
      · subst k; simpa [w₀] using dist_le_pi_dist x.1 y.1 j
      · simp [w₀,Function.update_of_ne hk]
    have hwy : dist w y ≤ dist x y := by
      change dist w₀ y.1 ≤ dist x.1 y.1
      apply (dist_pi_le_iff (dist_nonneg : 0≤dist x.1 y.1)).2
      intro k
      by_cases hk : k=j
      · subst k; simp [w₀]
      · simpa [w₀,Function.update_of_ne hk] using dist_le_pi_dist x.1 y.1 k
    have hx : dist (f x) (f w) ≤ B*dist x w :=
      hface i x w hi (by simp [w,w₀,Function.update_of_ne hij])
    have hy : dist (f w) (f y) ≤ B*dist w y :=
      hface j w y (by simpa [w,w₀] using hj) (by simp [w,w₀])
    have hx' := hx.trans (mul_le_mul_of_nonneg_left hxw B.2)
    have hy' := hy.trans (mul_le_mul_of_nonneg_left hwy B.2)
    have ht := dist_triangle (f x) (f w) (f y)
    have hc : 0 ≤ (C : ℝ)*dist x y := mul_nonneg C.2 dist_nonneg
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
    linarith

end

end AbelianTargets


