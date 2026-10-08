-- Prove2me | solution 1 for ConvexOptimization.barrier_method_sqrt_m_complexity_sc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-17T02:24:53.623325+00:00
-- url     : https://prove2.me/submissions/e006bf1d-89c7-4bdf-86ea-4e8b3960ef48

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_ConvexOptimization_IsDampedNewtonRunOn
import Definitions.Def_ConvexOptimization_logBarrier
import Theorems.Thm_ConvexOptimization_sc_newton_decrement_contraction
import Theorems.Thm_ConvexOptimization_sc_suboptimality_from_decrement
import Theorems.Thm_ConvexOptimization_two_phase_iteration_count_of_suboptimality
import Theorems.Thm_ConvexOptimization_barrier_centering_potential_gap

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Filter Topology InnerProductSpace
open ConvexOptimization

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000


-- ## The derivative of the Hessian field

namespace DHAux

variable {n : ℕ}

/-- The inverse Riesz identification, as a plain continuous linear map. -/
noncomputable def rieszInvL (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }

@[simp] theorem rieszInvL_apply (φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    rieszInvL n φ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ := rfl

/-- The Hessian field of a `C³` function is differentiable. -/
theorem hessian_differentiable
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf3 : ContDiffOn ℝ 3 f Ω)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x) :
    ∀ x ∈ Ω, DifferentiableAt ℝ H x := by
  -- `g` agrees with `rieszInvL ∘ fderiv f` on `Ω`
  have hgeq : ∀ y ∈ Ω, g y = rieszInvL n (fderiv ℝ f y) := by
    intro y hy
    have h1 : fderiv ℝ f y = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g y) :=
      (hg y hy).hasFDerivAt.fderiv
    rw [rieszInvL_apply, h1, LinearIsometryEquiv.symm_apply_apply]
  -- hence `g` is `C²` on `Ω`
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ f) Ω := hf3.fderiv_of_isOpen hΩo (by norm_num)
  have hgC : ContDiffOn ℝ 2 g Ω := by
    refine ContDiffOn.congr ?_ hgeq
    exact (rieszInvL n).contDiff.comp_contDiffOn hfd
  -- hence `fderiv g` is `C¹`, in particular differentiable, on `Ω`
  have hHeq : ∀ y ∈ Ω, H y = fderiv ℝ g y := fun y hy => (hH y hy).fderiv.symm
  have hfg : ContDiffOn ℝ 1 (fderiv ℝ g) Ω := hgC.fderiv_of_isOpen hΩo (by norm_num)
  have hdiff : DifferentiableOn ℝ (fderiv ℝ g) Ω := hfg.differentiableOn (by norm_num)
  intro x hx
  have hd : DifferentiableOn ℝ H Ω := hdiff.congr (fun y hy => (hHeq y hy))
  exact (hd x hx).differentiableAt (hΩo.mem_nhds hx)


noncomputable def rieszL (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) a)
      map_add' := fun a b => by ext w; simp [inner_add_left]
      map_smul' := fun c a => by ext w; simp [real_inner_smul_left] }

@[simp] theorem rieszL_apply (a b : EuclideanSpace ℝ (Fin n)) : rieszL n a b = ⟪a, b⟫ := rfl

/-- Evaluation of an operator against a fixed pair, as a continuous linear functional. -/
noncomputable def evalCLM (b c : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ => ⟪φ b, c⟫
      map_add' := fun φ ψ => by simp [inner_add_left]
      map_smul' := fun r φ => by simp [real_inner_smul_left] }

@[simp] theorem evalCLM_apply (b c : EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    evalCLM b c φ = ⟪φ b, c⟫ := rfl

variable (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

/-- Symmetry of the derivative of the Hessian field in its first two slots. -/
theorem DH_sym12 (hΩo : IsOpen Ω) (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (a b : EuclideanSpace ℝ (Fin n)) :
    DH a b = DH b a := by
  have hev : ∀ᶠ y in 𝓝 x, HasFDerivAt g (H y) y := by
    filter_upwards [hΩo.mem_nhds hx] with y hy using hH y hy
  exact second_derivative_symmetric_of_eventually hev hDH a b

/-- Symmetry of the derivative of the Hessian field in its last two slots. -/
theorem DH_sym23 (hΩo : IsOpen Ω) (hHsym : ∀ y ∈ Ω, ∀ a b, ⟪H y a, b⟫ = ⟪H y b, a⟫)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (a b c : EuclideanSpace ℝ (Fin n)) :
    ⟪DH a b, c⟫ = ⟪DH a c, b⟫ := by
  -- the function `y ↦ ⟪H y b, c⟫ - ⟪H y c, b⟫` vanishes near `x`
  set Ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ⟪H y b, c⟫ - ⟪H y c, b⟫ with hΨ
  have h1 : HasFDerivAt (fun y => ⟪H y b, c⟫)
      (((evalCLM b c) : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ).comp DH)
      x := (evalCLM b c).hasFDerivAt.comp x hDH
  have h2 : HasFDerivAt (fun y => ⟪H y c, b⟫)
      (((evalCLM c b) : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ).comp DH)
      x := (evalCLM c b).hasFDerivAt.comp x hDH
  have hΨd : HasFDerivAt Ψ ((evalCLM b c).comp DH - (evalCLM c b).comp DH) x := h1.sub h2
  have hzero : HasFDerivAt Ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    have hev : Ψ =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [hΩo.mem_nhds hx] with y hy
      simp only [hΨ]
      rw [hHsym y hy b c]
      ring
    exact (hasFDerivAt_const (0:ℝ) x).congr_of_eventuallyEq hev
  have hLzero : (evalCLM b c).comp DH - (evalCLM c b).comp DH = 0 := hΨd.unique hzero
  have hap := congrArg (fun (M : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) => M a) hLzero
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    evalCLM_apply, ContinuousLinearMap.zero_apply] at hap
  linarith [hap]

/-- The third derivative along a line, expressed through `DH`. -/
theorem iteratedDeriv3_eq (hΩo : IsOpen Ω)
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (v : EuclideanSpace ℝ (Fin n)) :
    iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0 = ⟪DH v v, v⟫ := by
  classical
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  set d1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hd1
  set d2 : ℝ → ℝ := fun t => ⟪H (x + t • v) v, v⟫ with hd2
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφd : ∀ t ∈ S, HasDerivAt φ (d1 t) t := by
    intro t ht
    have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t (hline t)
    simpa [hφ, hd1, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp
  have hd1d : ∀ t ∈ S, HasDerivAt d1 (d2 t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + t • v) v) t :=
      (hH _ ht).comp_hasDerivAt t (hline t)
    exact (h1.inner ℝ (hasDerivAt_const t v)).congr_deriv (by simp [hd2])
  have hev : ∀ t ∈ S, deriv φ =ᶠ[𝓝 t] d1 := by
    intro t ht
    filter_upwards [hSopen.mem_nhds ht] with s hs using (hφd s hs).deriv
  have hu2 : ∀ t ∈ S, iteratedDeriv 2 φ t = d2 t := by
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_one, (hev t ht).deriv_eq]
    exact (hd1d t ht).deriv
  have hev2 : iteratedDeriv 2 φ =ᶠ[𝓝 (0:ℝ)] d2 := by
    filter_upwards [hSopen.mem_nhds h0S] with s hs using hu2 s hs
  have hd2d : HasDerivAt d2 ⟪DH v v, v⟫ 0 := by
    have hcomp : HasDerivAt (fun t : ℝ => H (x + t • v)) (DH v) 0 := by
      have hDH' : HasFDerivAt H DH ((fun t : ℝ => x + t • v) 0) := by simpa using hDH
      have hc := hDH'.comp_hasDerivAt (0:ℝ) (hline 0)
      simpa using hc
    have := (hcomp.clm_apply (hasDerivAt_const (0:ℝ) v)).inner ℝ (hasDerivAt_const (0:ℝ) v)
    simpa [hd2] using this
  rw [iteratedDeriv_succ, hev2.deriv_eq, hd2d.deriv]


end DHAux

namespace DHAux

variable {m : ℕ}

/-- The second derivative along a line, expressed through the Hessian field. -/
theorem iteratedDeriv2_eq (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ Ω) (v : EuclideanSpace ℝ (Fin m)) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 = ⟪H x v, v⟫ := by
  classical
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  set d1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hd1
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφd : ∀ t ∈ S, HasDerivAt φ (d1 t) t := by
    intro t ht
    have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t (hline t)
    simpa [hφ, hd1, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp
  have hd1d : HasDerivAt d1 ⟪H x v, v⟫ 0 := by
    have h1 : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + (0:ℝ) • v) v) 0 :=
      (hH _ h0S).comp_hasDerivAt 0 (hline 0)
    have h2 := h1.inner ℝ (hasDerivAt_const (0:ℝ) v)
    simpa [hd1] using h2
  have hev : deriv φ =ᶠ[𝓝 (0:ℝ)] d1 := by
    filter_upwards [hSopen.mem_nhds h0S] with s hs using (hφd s hs).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  exact hd1d.deriv

/-- Differentiating the Hessian field along a line. -/
theorem hess_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (DHf : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hDH : ∀ y ∈ Ω, HasFDerivAt H (DHf y) y)
    (x v a b : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => ⟪H (x + s • v) a, b⟫) ⟪DHf (x + t • v) v a, b⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => H (x + s • v)) (DHf (x + t • v) v) t :=
    (hDH _ ht).comp_hasDerivAt t hline
  have h2 := (hcomp.clm_apply (hasDerivAt_const t a)).inner ℝ (hasDerivAt_const t b)
  simpa using h2

/-- Differentiating the gradient field along a line. -/
theorem grad_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hH : ∀ y ∈ Ω, HasFDerivAt g (H y) y)
    (x v b : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => ⟪g (x + s • v), b⟫) ⟪H (x + t • v) v, b⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + t • v) v) t :=
    (hH _ ht).comp_hasDerivAt t hline
  have h2 := hcomp.inner ℝ (hasDerivAt_const t b)
  simpa using h2

/-- Differentiating the function itself along a line. -/
theorem fun_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ y ∈ Ω, HasGradientAt f (g y) y)
    (x v : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪g (x + t • v), v⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t hline
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp

end DHAux


-- ## One-dimensional self-concordance comparison estimates

namespace SCUp

/-- **The one-dimensional self-concordance comparison.**  If `u > 0` is differentiable on an
interval containing `[0, b]` with `|u'| ≤ 2 u^{3/2}`, then with `r = √(u 0)`,

* `u t ≥ r²/(1 + r t)²`  (always), and
* `u t ≤ r²/(1 - r t)²`  (as long as `r t < 1`).

Both are obtained by noting that `ψ = u^{-1/2}` is `1`-Lipschitz. -/
theorem u_bounds (S : Set ℝ) (hSc : Convex ℝ S) (b : ℝ) (hb : 0 ≤ b)
    (hIcc : Set.Icc (0:ℝ) b ⊆ S)
    (u u' : ℝ → ℝ)
    (hud : ∀ t ∈ S, HasDerivAt u (u' t) t)
    (hupos : ∀ t ∈ S, 0 < u t)
    (hscb : ∀ t ∈ S, |u' t| ≤ 2 * (u t) ^ ((3:ℝ)/2)) :
    ∀ t ∈ Set.Icc (0:ℝ) b,
      (Real.sqrt (u 0)) ^ 2 / (1 + Real.sqrt (u 0) * t) ^ 2 ≤ u t ∧
      (Real.sqrt (u 0) * t < 1 →
        u t ≤ (Real.sqrt (u 0)) ^ 2 / (1 - Real.sqrt (u 0) * t) ^ 2) := by
  classical
  have h0S : (0:ℝ) ∈ S := hIcc ⟨le_refl 0, hb⟩
  set r : ℝ := Real.sqrt (u 0) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (hupos 0 h0S)
  have hr2 : r ^ 2 = u 0 := Real.sq_sqrt (hupos 0 h0S).le
  set ψ : ℝ → ℝ := fun t => (Real.sqrt (u t))⁻¹ with hψ
  have hsp : ∀ t ∈ S, 0 < Real.sqrt (u t) := fun t ht => Real.sqrt_pos.mpr (hupos t ht)
  have hsq : ∀ t ∈ S, Real.sqrt (u t) ^ 2 = u t := fun t ht => Real.sq_sqrt (hupos t ht).le
  have hψd : ∀ t ∈ S, HasDerivAt ψ (-(u' t / (2 * Real.sqrt (u t))) / (u t)) t := by
    intro t ht
    have hs : HasDerivAt (fun s => Real.sqrt (u s)) (u' t / (2 * Real.sqrt (u t))) t := by
      have h0 := (Real.hasDerivAt_sqrt (ne_of_gt (hupos t ht))).comp t (hud t ht)
      have heq : 1 / (2 * Real.sqrt (u t)) * u' t = u' t / (2 * Real.sqrt (u t)) := by ring
      rw [heq] at h0
      exact h0
    have hne : Real.sqrt (u t) ≠ 0 := ne_of_gt (hsp t ht)
    have hinv := hs.inv hne
    rw [hsq t ht] at hinv
    exact hinv
  have hψlip : ∀ t ∈ S, |(-(u' t / (2 * Real.sqrt (u t))) / (u t))| ≤ 1 := by
    intro t ht
    have hup := hupos t ht
    have hspt := hsp t ht
    have hbb := hscb t ht
    have hpow : (u t) ^ ((3:ℝ)/2) = u t * Real.sqrt (u t) := by
      rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hup, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hpow] at hbb
    rw [abs_div, abs_neg, abs_div, abs_of_pos hup,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (u t))]
    rw [div_div, div_le_one (by positivity)]
    calc |u' t| ≤ 2 * (u t * Real.sqrt (u t)) := hbb
      _ = 2 * Real.sqrt (u t) * u t := by ring
  -- `ψ t ≤ ψ 0 + t` and `ψ 0 - t ≤ ψ t` on `[0, b]`
  have hψ0 : ψ 0 = r⁻¹ := by rw [hψ, hr]
  have hupper : ∀ t ∈ Set.Icc (0:ℝ) b, ψ t ≤ ψ 0 + t := by
    have hanti : AntitoneOn (fun t => ψ t - t) (Set.Icc (0:ℝ) b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) ?_ ?_ ?_
      · intro t ht
        exact (((hψd t (hIcc ht)).sub (hasDerivAt_id t)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hψd t (hIcc (Set.mem_Icc_of_Ioo ht))).sub
          (hasDerivAt_id t)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htS : t ∈ S := hIcc (Set.mem_Icc_of_Ioo ht)
        have hd : HasDerivAt (fun s : ℝ => ψ s - s)
            (-(u' t / (2 * Real.sqrt (u t))) / (u t) - 1) t :=
          (hψd t htS).sub (hasDerivAt_id t)
        rw [hd.deriv]
        linarith [(abs_le.mp (hψlip t htS)).2]
    intro t ht
    have := hanti (Set.left_mem_Icc.mpr hb) ht ht.1
    simp only at this
    linarith
  have hlower : ∀ t ∈ Set.Icc (0:ℝ) b, ψ 0 - t ≤ ψ t := by
    have hmono : MonotoneOn (fun t => ψ t + t) (Set.Icc (0:ℝ) b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b) ?_ ?_ ?_
      · intro t ht
        exact (((hψd t (hIcc ht)).add (hasDerivAt_id t)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hψd t (hIcc (Set.mem_Icc_of_Ioo ht))).add
          (hasDerivAt_id t)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htS : t ∈ S := hIcc (Set.mem_Icc_of_Ioo ht)
        have hd : HasDerivAt (fun s : ℝ => ψ s + s)
            (-(u' t / (2 * Real.sqrt (u t))) / (u t) + 1) t :=
          (hψd t htS).add (hasDerivAt_id t)
        rw [hd.deriv]
        linarith [(abs_le.mp (hψlip t htS)).1]
    intro t ht
    have := hmono (Set.left_mem_Icc.mpr hb) ht ht.1
    simp only at this
    linarith
  intro t ht
  have htS : t ∈ S := hIcc ht
  have hspt := hsp t htS
  constructor
  · -- lower bound on `u`
    have hden : (0:ℝ) < 1 + r * t := by nlinarith only [ht.1, hrpos]
    have hb2 : (Real.sqrt (u t))⁻¹ ≤ (1 + r * t) / r := by
      have := hupper t ht
      rw [hψ0] at this
      calc (Real.sqrt (u t))⁻¹ ≤ r⁻¹ + t := this
        _ = (1 + r * t) / r := by field_simp
    have hkey : r / (1 + r * t) ≤ Real.sqrt (u t) := by
      rw [div_le_iff₀ hden]
      have h1 := mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hrpos hspt))
      rw [show (r * Real.sqrt (u t)) * (Real.sqrt (u t))⁻¹ = r by field_simp,
        show (r * Real.sqrt (u t)) * ((1 + r * t) / r) = Real.sqrt (u t) * (1 + r * t) by
          field_simp] at h1
      exact h1
    calc r ^ 2 / (1 + r * t) ^ 2 = (r / (1 + r * t)) ^ 2 := (div_pow r (1 + r * t) 2).symm
      _ ≤ (Real.sqrt (u t)) ^ 2 := pow_le_pow_left₀ (by positivity) hkey 2
      _ = u t := hsq t htS
  · -- upper bound on `u`
    intro hrt
    have hden : (0:ℝ) < 1 - r * t := by linarith
    have hb2 : (1 - r * t) / r ≤ (Real.sqrt (u t))⁻¹ := by
      have := hlower t ht
      rw [hψ0] at this
      calc (1 - r * t) / r = r⁻¹ - t := by field_simp
        _ ≤ (Real.sqrt (u t))⁻¹ := this
    have hkey : Real.sqrt (u t) ≤ r / (1 - r * t) := by
      rw [le_div_iff₀ hden]
      have h1 := mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hrpos hspt))
      rw [show (r * Real.sqrt (u t)) * ((1 - r * t) / r) = Real.sqrt (u t) * (1 - r * t) by
          field_simp,
        show (r * Real.sqrt (u t)) * (Real.sqrt (u t))⁻¹ = r by field_simp] at h1
      exact h1
    calc u t = (Real.sqrt (u t)) ^ 2 := (hsq t htS).symm
      _ ≤ (r / (1 - r * t)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hkey 2
      _ = r ^ 2 / (1 - r * t) ^ 2 := div_pow r (1 - r * t) 2

variable {n : ℕ}

/-- Gronwall-type comparison: `|q'/q| ≤ 2r/(1-rt)` forces `q` to stay within the factor
`(1-r)^{±2}`.  Proved by monotonicity of `log q ∓ 2 log (1 - r t)`, with no integration. -/
theorem log_comparison (S : Set ℝ) (hIcc : Set.Icc (0:ℝ) 1 ⊆ S)
    (q q' : ℝ → ℝ) (hqd : ∀ t ∈ S, HasDerivAt q (q' t) t) (hqpos : ∀ t ∈ S, 0 < q t)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbnd : ∀ t ∈ Set.Icc (0:ℝ) 1, |q' t| ≤ 2 * r / (1 - r * t) * q t) :
    (1 - r) ^ 2 * q 0 ≤ q 1 ∧ q 1 ≤ q 0 / (1 - r) ^ 2 := by
  classical
  have hden : ∀ t ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < 1 - r * t := by
    intro t ht
    nlinarith only [ht.1, ht.2, hr0, hr1]
  have hlogd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (1 - r * s)) (-r / (1 - r * t)) t := by
    intro t ht
    have hin : HasDerivAt (fun s : ℝ => 1 - r * s) (-r) t := by
      simpa using (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul r)
    exact hin.log (ne_of_gt (hden t ht))
  have hqld : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (q s)) (q' t / q t) t := fun t ht =>
    (hqd t (hIcc ht)).log (ne_of_gt (hqpos t (hIcc ht)))
  -- upper: `log q + 2 log (1 - r t)` is antitone
  have hup : q 1 ≤ q 0 / (1 - r) ^ 2 := by
    have hanti : AntitoneOn (fun t => Real.log (q t) + 2 * Real.log (1 - r * t))
        (Set.Icc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hqld t ht).add ((hlogd t ht).const_mul 2)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hqld t (Set.mem_Icc_of_Ioo ht)).add
          ((hlogd t (Set.mem_Icc_of_Ioo ht)).const_mul 2)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s => Real.log (q s) + 2 * Real.log (1 - r * s))
            (q' t / q t + 2 * (-r / (1 - r * t))) t := (hqld t htI).add ((hlogd t htI).const_mul 2)
        rw [hd.deriv]
        have hb := (abs_le.mp (hbnd t htI)).2
        have hqp := hqpos t (hIcc htI)
        have hdp := hden t htI
        have hle : q' t / q t ≤ 2 * r / (1 - r * t) := by
          rw [div_le_iff₀ hqp]
          exact hb
        have h2 : 2 * (-r / (1 - r * t)) = -(2 * r / (1 - r * t)) := by ring
        rw [h2]
        linarith [hle]
    have hcmp := hanti (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (by norm_num)
    simp only [mul_zero, mul_one, sub_zero, Real.log_one, mul_zero, add_zero] at hcmp
    have hq0 := hqpos 0 (hIcc (Set.left_mem_Icc.mpr (by norm_num)))
    have hq1 := hqpos 1 (hIcc (Set.right_mem_Icc.mpr (by norm_num)))
    have hrr : (0:ℝ) < 1 - r := by linarith
    have hlg : Real.log (q 1) + 2 * Real.log (1 - r) ≤ Real.log (q 0) := hcmp
    have hexp : Real.log (q 1 * (1 - r) ^ 2) ≤ Real.log (q 0) := by
      rw [Real.log_mul (ne_of_gt hq1) (by positivity), Real.log_pow]
      push_cast
      linarith
    have hAB : q 1 * (1 - r) ^ 2 ≤ q 0 := by
      have h1 : Real.exp (Real.log (q 1 * (1 - r) ^ 2)) ≤ Real.exp (Real.log (q 0)) :=
        Real.exp_le_exp.mpr hexp
      rwa [Real.exp_log (by positivity), Real.exp_log hq0] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith [hAB]
  -- lower: `log q - 2 log (1 - r t)` is monotone
  have hlow : (1 - r) ^ 2 * q 0 ≤ q 1 := by
    have hmono : MonotoneOn (fun t => Real.log (q t) - 2 * Real.log (1 - r * t))
        (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hqld t ht).sub ((hlogd t ht).const_mul 2)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hqld t (Set.mem_Icc_of_Ioo ht)).sub
          ((hlogd t (Set.mem_Icc_of_Ioo ht)).const_mul 2)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s => Real.log (q s) - 2 * Real.log (1 - r * s))
            (q' t / q t - 2 * (-r / (1 - r * t))) t := (hqld t htI).sub ((hlogd t htI).const_mul 2)
        rw [hd.deriv]
        have hb := (abs_le.mp (hbnd t htI)).1
        have hqp := hqpos t (hIcc htI)
        have hdp := hden t htI
        have hge : -(2 * r / (1 - r * t)) ≤ q' t / q t := by
          rw [le_div_iff₀ hqp]
          linarith [hb]
        have h2 : 2 * (-r / (1 - r * t)) = -(2 * r / (1 - r * t)) := by ring
        rw [h2]
        linarith [hge]
    have hcmp := hmono (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (by norm_num)
    simp only [mul_zero, mul_one, sub_zero, Real.log_one, mul_zero, sub_zero] at hcmp
    have hq0 := hqpos 0 (hIcc (Set.left_mem_Icc.mpr (by norm_num)))
    have hq1 := hqpos 1 (hIcc (Set.right_mem_Icc.mpr (by norm_num)))
    have hrr : (0:ℝ) < 1 - r := by linarith
    have hexp : Real.log ((1 - r) ^ 2 * q 0) ≤ Real.log (q 1) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hq0), Real.log_pow]
      push_cast
      linarith [hcmp]
    have h1 : Real.exp (Real.log ((1 - r) ^ 2 * q 0)) ≤ Real.exp (Real.log (q 1)) :=
      Real.exp_le_exp.mpr hexp
    rwa [Real.exp_log (by positivity), Real.exp_log hq1] at h1
  exact ⟨hlow, hup⟩

/-- A symmetric form dominated on the diagonal by `κ Q` is dominated off-diagonal too. -/
theorem sym_form_bound
    (Q D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hDsym : ∀ a b, ⟪D a, b⟫ = ⟪D b, a⟫)
    (hQpd : ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 → 0 < ⟪Q a, a⟫)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hdiag : ∀ a, |⟪D a, a⟫| ≤ κ * ⟪Q a, a⟫) :
    ∀ a b, |⟪D a, b⟫| ≤ κ * Real.sqrt ⟪Q a, a⟫ * Real.sqrt ⟪Q b, b⟫ := by
  classical
  have hQnn : ∀ a : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪Q a, a⟫ := by
    intro a
    by_cases h : a = 0
    · simp [h]
    · exact (hQpd a h).le
  -- polarisation
  have hpol : ∀ a b : EuclideanSpace ℝ (Fin n),
      |⟪D a, b⟫| ≤ κ / 2 * (⟪Q a, a⟫ + ⟪Q b, b⟫) := by
    intro a b
    have hexp : ⟪D (a + b), a + b⟫ - ⟪D (a - b), a - b⟫ = 4 * ⟪D a, b⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hDsym b a]
      ring
    have hQexp : ⟪Q (a + b), a + b⟫ + ⟪Q (a - b), a - b⟫ = 2 * (⟪Q a, a⟫ + ⟪Q b, b⟫) := by
      have hQsym : ∀ p q : EuclideanSpace ℝ (Fin n), ⟪Q p, q⟫ + ⟪Q q, p⟫
          = ⟪Q (p + q), p + q⟫ - ⟪Q p, p⟫ - ⟪Q q, q⟫ := by
        intro p q
        simp only [map_add, inner_add_left, inner_add_right]
        ring
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      ring
    have h1 := hdiag (a + b)
    have h2 := hdiag (a - b)
    have habs : |4 * ⟪D a, b⟫| ≤ |⟪D (a + b), a + b⟫| + |⟪D (a - b), a - b⟫| := by
      rw [← hexp, sub_eq_add_neg]
      calc |⟪D (a + b), a + b⟫ + -⟪D (a - b), a - b⟫|
          ≤ |⟪D (a + b), a + b⟫| + |-⟪D (a - b), a - b⟫| := abs_add_le _ _
        _ = |⟪D (a + b), a + b⟫| + |⟪D (a - b), a - b⟫| := by rw [abs_neg]
    rw [abs_mul, show |(4:ℝ)| = 4 by norm_num] at habs
    nlinarith only [habs, h1, h2, hQexp, hκ]
  intro a b
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hQa : 0 < ⟪Q a, a⟫ := hQpd a ha
  have hQb : 0 < ⟪Q b, b⟫ := hQpd b hb
  set sa := Real.sqrt ⟪Q a, a⟫ with hsa
  set sb := Real.sqrt ⟪Q b, b⟫ with hsb
  have hsap : 0 < sa := Real.sqrt_pos.mpr hQa
  have hsbp : 0 < sb := Real.sqrt_pos.mpr hQb
  have hsa2 : sa ^ 2 = ⟪Q a, a⟫ := Real.sq_sqrt hQa.le
  have hsb2 : sb ^ 2 = ⟪Q b, b⟫ := Real.sq_sqrt hQb.le
  set c : ℝ := Real.sqrt (sb / sa) with hc
  have hcp : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = sb / sa := Real.sq_sqrt (by positivity)
  have hkey := hpol (c • a) (c⁻¹ • b)
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, map_smul, real_inner_smul_left,
    real_inner_smul_right, map_smul, real_inner_smul_left, real_inner_smul_right] at hkey
  rw [show c * (c⁻¹ * ⟪D a, b⟫) = ⟪D a, b⟫ by field_simp] at hkey
  rw [show c * (c * ⟪Q a, a⟫) = c ^ 2 * ⟪Q a, a⟫ by ring,
    show c⁻¹ * (c⁻¹ * ⟪Q b, b⟫) = (c ^ 2)⁻¹ * ⟪Q b, b⟫ by field_simp] at hkey
  rw [hc2, ← hsa2, ← hsb2] at hkey
  have hsimp : sb / sa * sa ^ 2 + (sb / sa)⁻¹ * sb ^ 2 = 2 * (sa * sb) := by
    field_simp
    ring
  rw [hsimp] at hkey
  calc |⟪D a, b⟫| ≤ κ / 2 * (2 * (sa * sb)) := hkey
    _ = κ * sa * sb := by ring

end SCUp

namespace SCUp

/-- `log_comparison` on an arbitrary right endpoint `b`, obtained by rescaling. -/
theorem log_comparison' (S : Set ℝ) (b : ℝ) (hb : 0 ≤ b) (hIcc : Set.Icc (0:ℝ) b ⊆ S)
    (q q' : ℝ → ℝ) (hqd : ∀ t ∈ S, HasDerivAt q (q' t) t) (hqpos : ∀ t ∈ S, 0 < q t)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρb : ρ * b < 1)
    (hbnd : ∀ t ∈ Set.Icc (0:ℝ) b, |q' t| ≤ 2 * ρ / (1 - ρ * t) * q t) :
    (1 - ρ * b) ^ 2 * q 0 ≤ q b ∧ q b ≤ q 0 / (1 - ρ * b) ^ 2 := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst_vars
    simp
  -- rescale `t ↦ b t`
  set S' : Set ℝ := {t : ℝ | b * t ∈ S} with hS'
  have hIcc' : Set.Icc (0:ℝ) 1 ⊆ S' := by
    intro t ht
    have h1 : (0:ℝ) ≤ b * t := mul_nonneg hbpos.le ht.1
    have h2 : b * t ≤ b := by nlinarith only [ht.1, ht.2, hbpos]
    exact hIcc ⟨h1, h2⟩
  set Q : ℝ → ℝ := fun t => q (b * t) with hQ
  set Q' : ℝ → ℝ := fun t => b * q' (b * t) with hQ'
  have hQd : ∀ t ∈ S', HasDerivAt Q (Q' t) t := by
    intro t ht
    have hin : HasDerivAt (fun s : ℝ => b * s) b t := by
      simpa using (hasDerivAt_id t).const_mul b
    have := (hqd _ ht).comp t hin
    simpa [hQ, hQ', mul_comm] using this
  have hQpos : ∀ t ∈ S', 0 < Q t := fun t ht => hqpos _ ht
  have hbnd' : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |Q' t| ≤ 2 * (ρ * b) / (1 - (ρ * b) * t) * Q t := by
    intro t ht
    have hmem : b * t ∈ Set.Icc (0:ℝ) b := by
      refine ⟨mul_nonneg hbpos.le ht.1, ?_⟩
      nlinarith only [ht.1, ht.2, hbpos]
    have hden : (0:ℝ) < 1 - ρ * (b * t) := by
      nlinarith only [mul_nonneg (mul_nonneg hρ0 hbpos.le) (sub_nonneg.mpr ht.2), hρb]
    have h := hbnd _ hmem
    have habs : |Q' t| = b * |q' (b * t)| := by
      rw [hQ']
      simp only [abs_mul, abs_of_pos hbpos]
    rw [habs]
    have hrw : 2 * (ρ * b) / (1 - ρ * b * t) * Q t = b * (2 * ρ / (1 - ρ * (b * t)) * q (b * t)) := by
      rw [hQ]
      rw [show ρ * b * t = ρ * (b * t) by ring]
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left h hbpos.le
  have hmain := log_comparison S' hIcc' Q Q' hQd hQpos (ρ * b) (by positivity) hρb hbnd'
  simpa [hQ] using hmain

end SCUp


-- ## The self-concordant upper bound along a line (B&V 9.43)

namespace SCLU

variable {n : ℕ}

/-- `-s - log (1 - s) ≤ s² / (2 (1 - s))` on `[0, 1)`. -/
theorem log_upper {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    -s - Real.log (1 - s) ≤ s ^ 2 / (2 * (1 - s)) := by
  set ρ : ℝ → ℝ := fun r => r ^ 2 / (2 * (1 - r)) + r + Real.log (1 - r) with hρ
  have hden : ∀ r ∈ Set.Icc (0:ℝ) s, (0:ℝ) < 1 - r := by
    intro r hr; linarith [hr.1, hr.2]
  have hd : ∀ r ∈ Set.Icc (0:ℝ) s,
      HasDerivAt ρ (r ^ 2 / (2 * (1 - r) ^ 2)) r := by
    intro r hr
    have hr1 : (0:ℝ) < 1 - r := hden r hr
    have hlin : HasDerivAt (fun u : ℝ => 1 - u) (-1) r := by
      simpa using (hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)
    have hnum : HasDerivAt (fun u : ℝ => u ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have hden2 : HasDerivAt (fun u : ℝ => 2 * (1 - u)) (-2) r := by
      simpa using hlin.const_mul (2:ℝ)
    have hq : HasDerivAt (fun u : ℝ => u ^ 2 / (2 * (1 - u)))
        ((2 * r * (2 * (1 - r)) - r ^ 2 * (-2)) / (2 * (1 - r)) ^ 2) r :=
      hnum.div hden2 (by positivity)
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - r)) r :=
      hlin.log (ne_of_gt hr1)
    have h := (hq.add (hasDerivAt_id r)).add hlog
    refine h.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn ρ (Set.Icc (0:ℝ) s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s) ?_ ?_ ?_
    · intro r hr; exact ((hd r hr).continuousAt).continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hd r (Set.mem_Icc_of_Ioo hr)).differentiableAt).differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrI : r ∈ Set.Icc (0:ℝ) s := Set.mem_Icc_of_Ioo hr
      rw [(hd r hrI).deriv]
      have := hden r hrI
      positivity
  have hle := hmono (Set.left_mem_Icc.mpr h0) (Set.right_mem_Icc.mpr h0) h0
  have hρ0 : ρ 0 = 0 := by rw [hρ]; norm_num
  have hρs : ρ s = s ^ 2 / (2 * (1 - s)) + s + Real.log (1 - s) := rfl
  rw [hρ0, hρs] at hle
  linarith

/-- **The self-concordant upper bound along a line** (B&V (9.43)), together with the
Dikin-ellipsoid membership.  If `‖v‖_x = lam` and `lam * b < 1`, then `x + b • v` is still
in `Ω` and

`f (x + b v) ≤ f x + b ⟪g x, v⟫ - lam b - log (1 - lam b)`. -/
theorem line_upper
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (v : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam : lam ^ 2 = ⟪H x v, v⟫)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : lam * b < 1) :
    x + b • v ∈ Ω ∧
      f (x + b • v) ≤ f x + b * ⟪g x, v⟫ - lam * b - Real.log (1 - lam * b) := by
  classical
  by_cases hv0 : v = 0
  · subst hv0
    have hl : lam = 0 := by
      have : lam ^ 2 = 0 := by rw [hlam]; simp
      nlinarith only [this, hlam0]
    refine ⟨by simpa using hx, ?_⟩
    rw [hl]
    simp
  -- `lam > 0`
  have hlampos : 0 < lam := by
    have h := hHpd x hx v hv0
    nlinarith only [hlam, hlam0, h]
  -- the derivative of the Hessian field
  set DHf : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun y => fderiv ℝ H y with hDHf
  have hDH : ∀ y ∈ Ω, HasFDerivAt H (DHf y) y := fun y hy =>
    (DHAux.hessian_differentiable Ω hΩo f hsc.2.1 g hg H hH y hy).hasFDerivAt
  have hdiag : ∀ y ∈ Ω, ∀ w, |⟪DHf y w w, w⟫| ≤ 2 * (⟪H y w, w⟫) ^ ((3:ℝ)/2) := by
    intro y hy w
    have h3 := DHAux.iteratedDeriv3_eq (Ω := Ω) (f := f) (g := g) (H := H) hΩo hg hH y hy
      (DHf y) (hDH y hy) w
    have h2 := DHAux.iteratedDeriv2_eq Ω hΩo f g hg H hH y hy w
    have hbnd := hsc.2.2 y hy w
    rw [h3, h2] at hbnd
    exact hbnd
  -- the slice
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have hSconv : Convex ℝ S := by
    intro a ha c hc p q hp hq hpq
    have ha' : x + a • v ∈ Ω := ha
    have hc' : x + c • v ∈ Ω := hc
    have hmem : p • (x + a • v) + q • (x + c • v) ∈ Ω := hΩc ha' hc' hp hq hpq
    have hrw : p • (x + a • v) + q • (x + c • v) = x + (p * a + q * c) • v := by
      have h1 : p • (x + a • v) + q • (x + c • v) = (p + q) • x + (p * a + q * c) • v := by
        module
      rw [h1, hpq, one_smul]
    rw [hrw] at hmem
    exact hmem
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  set φ : ℝ → ℝ := fun t => ⟪H (x + t • v) v, v⟫ with hφdef
  set φ' : ℝ → ℝ := fun t => ⟪DHf (x + t • v) v v, v⟫ with hφ'def
  have hφd : ∀ t ∈ S, HasDerivAt φ (φ' t) t := fun t ht =>
    DHAux.hess_line_deriv Ω H DHf hDH x v v v t ht
  have hφpos : ∀ t ∈ S, 0 < φ t := fun t ht => hHpd _ ht v hv0
  have hφsc : ∀ t ∈ S, |φ' t| ≤ 2 * (φ t) ^ ((3:ℝ)/2) := fun t ht => hdiag _ ht v
  have hφ0 : φ 0 = lam ^ 2 := by
    show (⟪H (x + (0:ℝ) • v) v, v⟫ : ℝ) = lam ^ 2
    rw [show x + (0:ℝ) • v = x by simp]
    exact hlam.symm
  have hφub : ∀ c : ℝ, 0 ≤ c → Set.Icc (0:ℝ) c ⊆ S →
      ∀ t ∈ Set.Icc (0:ℝ) c, lam * t < 1 → φ t ≤ lam ^ 2 / (1 - lam * t) ^ 2 := by
    intro c hc hIccc t ht hlt
    have h := (SCUp.u_bounds S hSconv c hc hIccc φ φ' hφd hφpos hφsc t ht).2
    rw [hφ0, Real.sqrt_sq hlam0] at h
    exact h hlt
  -- the derivatives of `f` along the ray
  set D1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hD1def
  have hD1d : ∀ t ∈ S, HasDerivAt D1 (φ t) t := fun t ht =>
    DHAux.grad_line_deriv Ω g H hH x v v t ht
  have hFd : ∀ t ∈ S, HasDerivAt (fun r : ℝ => f (x + r • v)) (D1 t) t := fun t ht =>
    DHAux.fun_line_deriv Ω f g hg x v t ht
  have hD10 : D1 0 = ⟪g x, v⟫ := by
    show (⟪g (x + (0:ℝ) • v), v⟫ : ℝ) = ⟪g x, v⟫
    rw [show x + (0:ℝ) • v = x by simp]
  have h1lb : (0:ℝ) < 1 - lam * b := by linarith
  -- ## the Dikin ellipsoid: `[0, b] ⊆ S`
  have hbS : b ∈ S := by
    by_contra hbnotS
    set A : Set ℝ := S ∩ Set.Icc (0:ℝ) b with hA
    have hA0 : (0:ℝ) ∈ A := ⟨h0S, ⟨le_refl 0, hb0⟩⟩
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hAbdd : BddAbove A := ⟨b, fun z hz => hz.2.2⟩
    set T : ℝ := sSup A with hTdef
    have hT0 : (0:ℝ) ≤ T := le_csSup hAbdd hA0
    have hTb : T ≤ b := csSup_le hAne (fun z hz => hz.2.2)
    have hsub : ∀ t : ℝ, 0 ≤ t → t < T → t ∈ S := by
      intro t ht0 htT
      obtain ⟨s, hsA, hts⟩ := exists_lt_of_lt_csSup hAne htT
      have hspos : (0:ℝ) < s := lt_of_le_of_lt ht0 hts
      have hc1 : (0:ℝ) ≤ 1 - t / s := by
        have h := (div_le_one hspos).mpr hts.le
        linarith
      have hc2 : (0:ℝ) ≤ t / s := div_nonneg ht0 hspos.le
      have hmem := hSconv h0S hsA.1 hc1 hc2 (by ring)
      have hrw : (1 - t / s) • (0:ℝ) + (t / s) • s = t := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rwa [hrw] at hmem
    have hTS : T ∉ S := by
      intro hTmem
      rcases eq_or_lt_of_le hTb with hTeq | hTlt
      · exact hbnotS (hTeq ▸ hTmem)
      · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hSopen T hTmem
        have hTu : T < min (T + δ / 2) b := lt_min (by linarith) hTlt
        have huS : min (T + δ / 2) b ∈ S := by
          refine hball ?_
          simp only [Metric.mem_ball, Real.dist_eq]
          have h1 : min (T + δ / 2) b ≤ T + δ / 2 := min_le_left _ _
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ min (T + δ / 2) b - T)]
          linarith
        have huA : min (T + δ / 2) b ∈ A := ⟨huS, ⟨by linarith, min_le_right _ _⟩⟩
        have hle := le_csSup hAbdd huA
        linarith
    have hTpos : (0:ℝ) < T := lt_of_le_of_ne hT0 (fun h => hTS (h ▸ h0S))
    set C : ℝ := lam ^ 2 / (1 - lam * b) ^ 2 with hC
    have hCnn : (0:ℝ) ≤ C := by rw [hC]; positivity
    set c : ℝ := f x + |⟪g x, v⟫| * b + C * b ^ 2 / 2 with hcdef
    have hkey : ∀ r : ℝ, 0 ≤ r → r < T → f (x + r • v) ≤ c := by
      intro r hr hrT
      have hIccr : Set.Icc (0:ℝ) r ⊆ S := fun s hs => hsub s hs.1 (lt_of_le_of_lt hs.2 hrT)
      have hrb : r ≤ b := le_trans hrT.le hTb
      have hφC : ∀ s ∈ Set.Icc (0:ℝ) r, φ s ≤ C := by
        intro s hs
        have hsb : s ≤ b := le_trans hs.2 hrb
        have hlt : lam * s < 1 := by
          have := mul_le_mul_of_nonneg_left hsb hlam0
          linarith
        have h1 := hφub r hr hIccr s hs hlt
        have hd1 : (0:ℝ) < 1 - lam * s := by linarith
        have hd2 : 1 - lam * b ≤ 1 - lam * s := by
          have := mul_le_mul_of_nonneg_left hsb hlam0
          linarith
        have hsq : (1 - lam * b) ^ 2 ≤ (1 - lam * s) ^ 2 := pow_le_pow_left₀ h1lb.le hd2 2
        have h2 : lam ^ 2 / (1 - lam * s) ^ 2 ≤ C := by
          rw [hC, div_le_div_iff₀ (pow_pos hd1 2) (pow_pos h1lb 2)]
          nlinarith only [mul_le_mul_of_nonneg_left hsq (sq_nonneg lam)]
        linarith
      have hstep1 : ∀ s ∈ Set.Icc (0:ℝ) r, D1 s ≤ D1 0 + C * s := by
        have hlin : ∀ s : ℝ, HasDerivAt (fun u : ℝ => C * u) C s := by
          intro s; simpa using (hasDerivAt_id s).const_mul C
        have hanti : AntitoneOn (fun s => D1 s - C * s) (Set.Icc (0:ℝ) r) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) ?_ ?_ ?_
          · intro s hs
            exact (((hD1d s (hIccr hs)).sub (hlin s)).continuousAt).continuousWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            exact (((hD1d s (hIccr (Set.mem_Icc_of_Ioo hs))).sub
              (hlin s)).differentiableAt).differentiableWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hsI : s ∈ Set.Icc (0:ℝ) r := Set.mem_Icc_of_Ioo hs
            have hd : HasDerivAt (fun u : ℝ => D1 u - C * u) (φ s - C) s :=
              (hD1d s (hIccr hsI)).sub (hlin s)
            rw [hd.deriv]
            linarith [hφC s hsI]
        intro s hs
        have h := hanti (Set.left_mem_Icc.mpr hr) hs hs.1
        simp only [mul_zero, sub_zero] at h
        linarith
      have hstep2 : f (x + r • v) ≤ f x + D1 0 * r + C * r ^ 2 / 2 := by
        have hlin2 : ∀ s : ℝ,
            HasDerivAt (fun u : ℝ => D1 0 * u + C * u ^ 2 / 2) (D1 0 + C * s) s := by
          intro s
          have h1 : HasDerivAt (fun u : ℝ => D1 0 * u) (D1 0) s := by
            simpa using (hasDerivAt_id s).const_mul (D1 0)
          have h2 : HasDerivAt (fun u : ℝ => C * u ^ 2 / 2) (C * s) s := by
            have h := ((hasDerivAt_pow 2 s).const_mul C).div_const 2
            refine h.congr_deriv ?_
            push_cast
            ring
          exact h1.add h2
        have hanti : AntitoneOn (fun s => f (x + s • v) - (D1 0 * s + C * s ^ 2 / 2))
            (Set.Icc (0:ℝ) r) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) ?_ ?_ ?_
          · intro s hs
            exact (((hFd s (hIccr hs)).sub (hlin2 s)).continuousAt).continuousWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            exact (((hFd s (hIccr (Set.mem_Icc_of_Ioo hs))).sub
              (hlin2 s)).differentiableAt).differentiableWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hsI : s ∈ Set.Icc (0:ℝ) r := Set.mem_Icc_of_Ioo hs
            have hd : HasDerivAt (fun u : ℝ => f (x + u • v) - (D1 0 * u + C * u ^ 2 / 2))
                (D1 s - (D1 0 + C * s)) s := (hFd s (hIccr hsI)).sub (hlin2 s)
            rw [hd.deriv]
            linarith [hstep1 s hsI]
        have h := hanti (Set.left_mem_Icc.mpr hr) (Set.right_mem_Icc.mpr hr) hr
        simp only [zero_smul, add_zero, mul_zero, zero_add] at h
        norm_num at h
        linarith
      have habs : D1 0 * r ≤ |⟪g x, v⟫| * b := by
        rw [hD10]
        nlinarith only [le_abs_self ⟪g x, v⟫, abs_nonneg ⟪g x, v⟫, hr, hrb]
      have hCb : C * r ^ 2 / 2 ≤ C * b ^ 2 / 2 := by
        nlinarith only [mul_nonneg hCnn (sub_nonneg.mpr (pow_le_pow_left₀ hr hrb 2))]
      rw [hcdef]
      linarith
    have htend : Filter.Tendsto (fun t : ℝ => x + t • v) (𝓝[<] T) (𝓝 (x + T • v)) :=
      (Continuous.tendsto (by fun_prop) T).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] T, (x + t • v) ∈ {y | y ∈ Ω ∧ f y ≤ c} := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hTpos).filter_mono nhdsWithin_le_nhds] with t ht1 ht2
      exact ⟨hsub t ht2.le ht1, hkey t ht2.le ht1⟩
    exact hTS ((hclosed c).mem_of_tendsto htend hev).1
  have hIccb : Set.Icc (0:ℝ) b ⊆ S := by
    rcases eq_or_lt_of_le hb0 with hbz | hbpos
    · intro t ht
      have hb' := ht.2
      rw [← hbz] at hb'
      have ht0 : t = 0 := le_antisymm hb' ht.1
      rw [ht0]; exact h0S
    · intro t ht
      have hbne : b ≠ 0 := ne_of_gt hbpos
      have hc1 : (0:ℝ) ≤ (b - t) / b := div_nonneg (by linarith [ht.2]) hbpos.le
      have hc2 : (0:ℝ) ≤ t / b := div_nonneg ht.1 hbpos.le
      have hsum : (b - t) / b + t / b = 1 := by field_simp <;> ring
      have h := hSconv h0S hbS hc1 hc2 hsum
      have hrw : ((b - t) / b) • (0:ℝ) + (t / b) • b = t := by
        rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
        field_simp
      rwa [hrw] at h
  refine ⟨hIccb ⟨hb0, le_refl b⟩, ?_⟩
  -- ## the upper bound
  set M : ℝ → ℝ := fun t => f x + t * ⟪g x, v⟫ - lam * t - Real.log (1 - lam * t) with hM
  have hden : ∀ t ∈ Set.Icc (0:ℝ) b, (0:ℝ) < 1 - lam * t := by
    intro t ht
    have := mul_le_mul_of_nonneg_left ht.2 hlam0
    linarith
  have hMd : ∀ t ∈ Set.Icc (0:ℝ) b,
      HasDerivAt M (⟪g x, v⟫ - lam + lam / (1 - lam * t)) t := by
    intro t ht
    have hd := hden t ht
    have h1 : HasDerivAt (fun u : ℝ => f x + u * ⟪g x, v⟫ - lam * u) (⟪g x, v⟫ - lam) t := by
      have ha : HasDerivAt (fun u : ℝ => f x + u * ⟪g x, v⟫) (⟪g x, v⟫) t := by
        simpa using ((hasDerivAt_id t).mul_const ⟪g x, v⟫).const_add (f x)
      have hb2 : HasDerivAt (fun u : ℝ => lam * u) lam t := by
        simpa using (hasDerivAt_id t).const_mul lam
      simpa using ha.sub hb2
    have hlin : HasDerivAt (fun u : ℝ => 1 - lam * u) (-lam) t := by
      simpa using (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul lam)
    have h2 : HasDerivAt (fun u : ℝ => Real.log (1 - lam * u)) (-lam / (1 - lam * t)) t :=
      hlin.log (ne_of_gt hd)
    have h := h1.sub h2
    refine h.congr_deriv ?_
    rw [neg_div]
    ring
  -- the first derivative of `M - f∘line` is nonnegative
  set D : ℝ → ℝ := fun t => ⟪g x, v⟫ - lam + lam / (1 - lam * t) - D1 t with hD
  have hDnn : ∀ t ∈ Set.Icc (0:ℝ) b, 0 ≤ D t := by
    have hDd : ∀ t ∈ Set.Icc (0:ℝ) b,
        HasDerivAt D (lam ^ 2 / (1 - lam * t) ^ 2 - φ t) t := by
      intro t ht
      have hd := hden t ht
      have hlin : HasDerivAt (fun u : ℝ => 1 - lam * u) (-lam) t := by
        simpa using (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul lam)
      have hinv : HasDerivAt (fun u : ℝ => lam / (1 - lam * u))
          (-(lam * (-lam)) / (1 - lam * t) ^ 2) t := by
        have h := (hlin.inv (ne_of_gt hd)).const_mul lam
        refine h.congr_deriv ?_
        field_simp
      have h1 : HasDerivAt (fun u : ℝ => ⟪g x, v⟫ - lam + lam / (1 - lam * u))
          (-(lam * (-lam)) / (1 - lam * t) ^ 2) t := by
        simpa using hinv.const_add (⟪g x, v⟫ - lam)
      have h := h1.sub (hD1d t (hIccb ht))
      refine h.congr_deriv ?_
      ring
    have hmono : MonotoneOn D (Set.Icc (0:ℝ) b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b) ?_ ?_ ?_
      · intro t ht; exact ((hDd t ht).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact ((hDd t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) b := Set.mem_Icc_of_Ioo ht
        rw [(hDd t htI).deriv]
        have h1 := hφub b hb0 hIccb t htI
          (by have := mul_le_mul_of_nonneg_left htI.2 hlam0; linarith)
        linarith
    intro t ht
    have h := hmono (Set.left_mem_Icc.mpr hb0) ht ht.1
    have hD0 : D 0 = 0 := by
      show (⟪g x, v⟫ - lam + lam / (1 - lam * 0) - D1 0 : ℝ) = 0
      rw [hD10]; norm_num
    linarith [hD0 ▸ h]
  have hfinal : MonotoneOn (fun t => M t - f (x + t • v)) (Set.Icc (0:ℝ) b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b) ?_ ?_ ?_
    · intro t ht
      exact (((hMd t ht).sub (hFd t (hIccb ht))).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (((hMd t (Set.mem_Icc_of_Ioo ht)).sub
        (hFd t (hIccb (Set.mem_Icc_of_Ioo ht)))).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Set.Icc (0:ℝ) b := Set.mem_Icc_of_Ioo ht
      have hd : HasDerivAt (fun u : ℝ => M u - f (x + u • v))
          ((⟪g x, v⟫ - lam + lam / (1 - lam * t)) - D1 t) t :=
        (hMd t htI).sub (hFd t (hIccb htI))
      rw [hd.deriv]
      exact hDnn t htI
  have h := hfinal (Set.left_mem_Icc.mpr hb0) (Set.right_mem_Icc.mpr hb0) hb0
  have hM0 : M 0 = f x := by
    show (f x + (0:ℝ) * ⟪g x, v⟫ - lam * 0 - Real.log (1 - lam * 0) : ℝ) = f x
    norm_num
  have hx0' : f (x + (0:ℝ) • v) = f x := by rw [show x + (0:ℝ) • v = x by simp]
  simp only at h
  rw [hM0, hx0'] at h
  have hMb : M b = f x + b * ⟪g x, v⟫ - lam * b - Real.log (1 - lam * b) := rfl
  rw [hMb] at h
  linarith

end SCLU


-- ## The domain-confined backtracking line search

namespace SCBT

variable {n : ℕ}

/-- The trial point at `t` is feasible and Armijo-acceptable, for every
`t` with `t (1 + 2(1-α) λ) ≤ 2(1-α)`.  This is B&V's estimate (9.52)–(9.53). -/
theorem cond_of_le
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (α : ℝ) (hα0 : 0 < α) (hα : α < 1 / 2)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪H x Δ, Δ⟫)
    (t : ℝ) (ht0 : 0 ≤ t) (htau : t * (1 + 2 * (1 - α) * lam) ≤ 2 * (1 - α)) :
    x + t • Δ ∈ Ω ∧ f (x + t • Δ) ≤ f x + α * t * ⟪g x, Δ⟫ := by
  have hip : (⟪g x, Δ⟫ : ℝ) = -lam ^ 2 := by
    have h : (⟪H x Δ, Δ⟫ : ℝ) = -⟪g x, Δ⟫ := by rw [hΔ]; simp
    rw [hlam, h]; ring
  have hA : (0:ℝ) < 2 * (1 - α) := by linarith
  have hlt : lam * t < 1 := by
    rcases eq_or_lt_of_le ht0 with ht | ht
    · rw [← ht]; simpa using zero_lt_one
    · nlinarith only [htau, ht, hlam0, hα, hα0]
  obtain ⟨hmem, hup⟩ := SCLU.line_upper Ω hΩo hΩc f hsc g hg H hH hHpd hclosed x hx Δ lam
    hlam0 hlam t ht0 hlt
  refine ⟨hmem, ?_⟩
  have hlog := SCLU.log_upper (s := lam * t) (mul_nonneg hlam0 ht0) hlt
  have hden : (0:ℝ) < 1 - lam * t := by linarith
  -- `(lam t)^2 / (2 (1 - lam t)) ≤ (1 - α) t lam^2`
  have hkey : (lam * t) ^ 2 / (2 * (1 - lam * t)) ≤ (1 - α) * t * lam ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [htau, ht0, hlam0, hden, hA,
      mul_nonneg (mul_nonneg ht0 hlam0) hlam0,
      mul_nonneg (mul_nonneg (mul_nonneg ht0 ht0) hlam0) hlam0]
  rw [hip] at hup ⊢
  nlinarith only [hup, hlog, hkey]

/-- Every grid point below the threshold is admissible, so the line search always has an
admissible step. -/
theorem exists_step
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (α β : ℝ) (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪H x Δ, Δ⟫) :
    ∃ t : ℝ, IsBacktrackingStepOn Ω f g α β x Δ t := by
  classical
  set τ : ℝ := 2 * (1 - α) / (1 + 2 * (1 - α) * lam) with hτ
  have hA : (0:ℝ) < 2 * (1 - α) := by linarith
  have hd : (0:ℝ) < 1 + 2 * (1 - α) * lam := by nlinarith only [hlam0, hα, hα0]
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hcond : ∀ s : ℝ, 0 ≤ s → s ≤ τ →
      (x + s • Δ ∈ Ω ∧ f (x + s • Δ) ≤ f x + α * s * ⟪g x, Δ⟫) := by
    intro s hs0 hsτ
    refine cond_of_le Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α hα0 hα x hx Δ hΔ lam
      hlam0 hlam s hs0 ?_
    rw [hτ, le_div_iff₀ hd] at hsτ
    linarith
  set P : ℕ → Prop := fun j =>
    (x + (β ^ j) • Δ ∈ Ω ∧ f (x + (β ^ j) • Δ) ≤ f x + α * β ^ j * ⟪g x, Δ⟫) with hP
  have hex : ∃ j, P j := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hτpos hβ1
    exact ⟨j, hcond (β ^ j) (by positivity) hj.le⟩
  have hfind := Nat.find_spec hex
  refine ⟨β ^ (Nat.find hex), ⟨Nat.find hex, rfl⟩, hfind, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · left; rw [h0]; norm_num
  · right
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hnot := Nat.find_min hex (m := m) (by omega)
    have hrw : β ^ Nat.find hex / β = β ^ m := by
      rw [hm, pow_succ]; field_simp
    rw [hrw]
    exact hnot

/-- The line search never returns a step smaller than `β / (1 + λ)` (B&V p. 503). -/
theorem step_lower
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (α β : ℝ) (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪H x Δ, Δ⟫)
    (t : ℝ) (hbt : IsBacktrackingStepOn Ω f g α β x Δ t) :
    β / (1 + lam) ≤ t := by
  classical
  obtain ⟨⟨j, hj⟩, hcond, hlast⟩ := hbt
  have hA : (0:ℝ) < 2 * (1 - α) := by linarith
  have hd : (0:ℝ) < 1 + 2 * (1 - α) * lam := by nlinarith only [hlam0, hα, hα0]
  have hlam1 : (0:ℝ) < 1 + lam := by linarith
  set τ : ℝ := 2 * (1 - α) / (1 + 2 * (1 - α) * lam) with hτ
  have hhatτ : 1 / (1 + lam) ≤ τ := by
    rw [hτ, div_le_div_iff₀ hlam1 hd]
    nlinarith only [hlam0, hα, hα0]
  have hcondle : ∀ s : ℝ, 0 ≤ s → s ≤ τ →
      (x + s • Δ ∈ Ω ∧ f (x + s • Δ) ≤ f x + α * s * ⟪g x, Δ⟫) := by
    intro s hs0 hsτ
    refine cond_of_le Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α hα0 hα x hx Δ hΔ lam
      hlam0 hlam s hs0 ?_
    rw [hτ, le_div_iff₀ hd] at hsτ
    linarith
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [hj, h0, pow_zero]
    rw [div_le_one hlam1]
    linarith
  · rcases hlast with h1 | hnot
    · rw [h1, div_le_one hlam1]; linarith
    · -- the previous grid point failed, so it exceeded the threshold
      obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hprev : β ^ m = t / β := by
        rw [hj, hm, pow_succ]; field_simp
      have hgt : τ < t / β := by
        by_contra hle
        push_neg at hle
        exact hnot (hcondle (t / β) (by rw [← hprev]; positivity) hle)
      have h1 : 1 / (1 + lam) < t / β := lt_of_le_of_lt hhatτ hgt
      rw [div_lt_div_iff₀ hlam1 hβ0] at h1
      rw [div_le_iff₀ hlam1]
      linarith

/-- When the Newton decrement is below `(1-2α)/4`, every grid point is admissible, so the
line search must return the unit step (B&V (9.54)). -/
theorem step_unit
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (α β : ℝ) (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪H x Δ, Δ⟫)
    (hsmall : lam ≤ (1 - 2 * α) / 4)
    (t : ℝ) (hbt : IsBacktrackingStepOn Ω f g α β x Δ t) :
    t = 1 := by
  classical
  obtain ⟨⟨j, hj⟩, hcond, hlast⟩ := hbt
  have hA : (0:ℝ) < 2 * (1 - α) := by linarith
  have hall : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (x + s • Δ ∈ Ω ∧ f (x + s • Δ) ≤ f x + α * s * ⟪g x, Δ⟫) := by
    intro s hs0 hs1
    refine cond_of_le Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α hα0 hα x hx Δ hΔ lam
      hlam0 hlam s hs0 ?_
    have hpos1 : (0:ℝ) < 1 + 2 * (1 - α) * lam := by nlinarith only [hlam0, hα, hα0]
    have h2 := mul_le_mul_of_nonneg_right hs1 hpos1.le
    have h3 : 2 * (1 - α) * lam ≤ 1 - 2 * α := by
      nlinarith only [mul_le_mul_of_nonneg_left hsmall (by linarith : (0:ℝ) ≤ 2 * (1 - α)),
        hα, hα0]
    linarith
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [hj, h0, pow_zero]
  · exfalso
    have hne : t ≠ 1 := by
      rw [hj]
      have : β ^ j ≤ β := by
        calc β ^ j ≤ β ^ 1 := pow_le_pow_of_le_one hβ0.le hβ1.le (by omega)
          _ = β := pow_one β
      intro h; rw [h] at this; linarith
    rcases hlast with h1 | hnot
    · exact hne h1
    · refine hnot (hall (t / β) ?_ ?_)
      · rw [hj]; positivity
      · obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        rw [hj, hm, pow_succ, show β ^ m * β / β = β ^ m by field_simp]
        calc β ^ m ≤ β ^ 0 := pow_le_pow_of_le_one hβ0.le hβ1.le (Nat.zero_le m)
          _ = 1 := pow_zero β

end SCBT


-- ## The Newton iteration bound (B&V 9.56)

namespace SCIT

variable {n : ℕ}

/-- A positive definite operator on a finite-dimensional space is surjective, so the Newton
system always has a solution. -/
theorem newton_dir
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hpd : ∀ v, v ≠ 0 → 0 < ⟪A v, v⟫) (w : EuclideanSpace ℝ (Fin n)) :
    ∃ u, A u = w := by
  have hinj : Function.Injective (A.toLinearMap) := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : A (a - b) = 0 := by
      have h : A a = A b := hab
      simp only [map_sub, h, sub_self]
    have hp := hpd (a - b) hd
    rw [h0] at hp
    simp at hp
  exact (LinearMap.injective_iff_surjective.mp hinj) w

/-- `λ ↦ λ²/(1+λ)` is monotone on `[0, ∞)`. -/
theorem sq_div_succ_mono {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    a ^ 2 / (1 + a) ≤ c ^ 2 / (1 + c) := by
  have h1 : (0:ℝ) < 1 + a := by linarith
  have h2 : (0:ℝ) < 1 + c := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith only [ha, hac, mul_nonneg ha (sub_nonneg.mpr hac)]

/-- **B&V (9.56)** with the domain-confined line search. -/
theorem iteration_bound (α β ε : ℝ)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ Ω)
    (hstar : IsMinOn f Ω xstar)
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (hclosed : ∀ c : ℝ, IsClosed {x | x ∈ Ω ∧ f x ≤ c}) :
    ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (K : ℕ),
      x 0 = x0 ∧ IsDampedNewtonRunOn Ω f g H α β x ∧
      (K : ℝ) ≤ (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) * (f x0 - f xstar) +
        Real.logb 2 (Real.logb 2 (1 / ε)) + 1 ∧
      f (x K) - f xstar ≤ ε := by
  classical
  set η : ℝ := (1 - 2 * α) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη4 : η ≤ 1 / 4 := by rw [hη]; linarith
  have hη1 : (0:ℝ) < 1 - η := by linarith
  set γ : ℝ := α * β * η ^ 2 / (1 + η) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have h20 : (0:ℝ) < 20 - 8 * α := by linarith
  have h5 : (0:ℝ) < 5 - 2 * α := by linarith
  have hγeq : γ = α * β * (1 - 2 * α) ^ 2 / (20 - 8 * α) := by
    have hne : (20:ℝ) - 8 * α ≠ 0 := ne_of_gt h20
    have hpos2 : (0:ℝ) < 1 + (1 - 2 * α) / 4 := by linarith
    rw [hγ, hη, div_eq_div_iff (ne_of_gt hpos2) hne]
    ring
  -- ## the nonnegativity of the Hessian form
  have hHnn : ∀ y ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H y v, v⟫ := by
    intro y hy v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hHpd y hy v hv).le
  -- ## the Newton direction, as a function
  have hdirex : ∀ y : EuclideanSpace ℝ (Fin n),
      ∃ d : EuclideanSpace ℝ (Fin n), y ∈ Ω → H y d = -g y := by
    intro y
    by_cases hy : y ∈ Ω
    · obtain ⟨d, hd⟩ := newton_dir (H y) (hHpd y hy) (-g y)
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose Δof hΔof using hdirex
  set lamOf : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => Real.sqrt ⟪H y (Δof y), Δof y⟫ with hlamOf
  have hlam0 : ∀ y, 0 ≤ lamOf y := fun y => Real.sqrt_nonneg _
  have hlamsq : ∀ y ∈ Ω, (lamOf y) ^ 2 = ⟪H y (Δof y), Δof y⟫ := by
    intro y hy
    exact Real.sq_sqrt (hHnn y hy (Δof y))
  have hlamg : ∀ y ∈ Ω, (lamOf y) ^ 2 = ⟪g y, -(Δof y)⟫ := by
    intro y hy
    rw [hlamsq y hy, hΔof y hy]
    simp
  -- ## one step of the run
  have hstepex : ∀ y : EuclideanSpace ℝ (Fin n), ∃ z : EuclideanSpace ℝ (Fin n),
      y ∈ Ω → ∃ t : ℝ, IsBacktrackingStepOn Ω f g α β y (Δof y) t ∧ z = y + t • Δof y := by
    intro y
    by_cases hy : y ∈ Ω
    · obtain ⟨t, ht⟩ := SCBT.exists_step Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α β
        hα0 hα hβ0 hβ1 y hy (Δof y) (hΔof y hy) (lamOf y) (hlam0 y) (hlamsq y hy)
      exact ⟨y + t • Δof y, fun _ => ⟨t, ht, rfl⟩⟩
    · exact ⟨y, fun h => absurd h hy⟩
  choose nxt hnxt using hstepex
  set xs : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun k => Nat.rec (motive := fun _ => EuclideanSpace ℝ (Fin n)) x0 (fun _ y => nxt y) k
    with hxs
  have hxs0 : xs 0 = x0 := rfl
  have hxssucc : ∀ k, xs (k + 1) = nxt (xs k) := fun _ => rfl
  have hxsmem : ∀ k, xs k ∈ Ω := by
    intro k
    induction k with
    | zero => exact hx0
    | succ m ih =>
      obtain ⟨t, hbt, hz⟩ := hnxt (xs m) ih
      rw [hxssucc m, hz]
      exact hbt.2.1.1
  have hrun : IsDampedNewtonRunOn Ω f g H α β xs := by
    intro k
    refine ⟨hxsmem k, ?_⟩
    obtain ⟨t, hbt, hz⟩ := hnxt (xs k) (hxsmem k)
    exact ⟨Δof (xs k), t, hΔof _ (hxsmem k), hbt, by rw [hxssucc k]; exact hz⟩
  -- ## the two sequences
  set gap : ℕ → ℝ := fun k => f (xs k) - f xstar with hgapdef
  have hgapnn : ∀ k, 0 ≤ gap k := by
    intro k
    have := hstar (hxsmem k)
    simp only [hgapdef, sub_nonneg]
    exact this
  set meas : ℕ → ℝ := fun k => max (lamOf (xs k)) (Real.sqrt (gap k)) with hmeasdef
  have hmeasnn : ∀ k, 0 ≤ meas k := fun k => le_trans (hlam0 (xs k)) (le_max_left _ _)
  have hsub : ∀ k, gap k ≤ meas k ^ 2 := by
    intro k
    have h1 : Real.sqrt (gap k) ≤ meas k := le_max_right _ _
    have h2 : (Real.sqrt (gap k)) ^ 2 ≤ meas k ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (hgapnn k)] at h2
  -- suboptimality bound (B&V (9.50)) whenever the decrement is small
  have hsubopt : ∀ k, lamOf (xs k) ≤ 0.68 → gap k ≤ (lamOf (xs k)) ^ 2 := by
    intro k hk
    exact ConvexOptimization.sc_suboptimality_from_decrement Ω hΩo hΩc f hsc g hg H hH hHpd
      xstar hxstar hstar (xs k) (hxsmem k) (Δof (xs k)) (hΔof _ (hxsmem k))
      (lamOf (xs k)) (hlam0 _) (hlamg _ (hxsmem k)) hk
  have hmeas_eq : ∀ k, lamOf (xs k) < η → meas k = lamOf (xs k) := by
    intro k hk
    have hle : lamOf (xs k) ≤ 0.68 := by linarith [hη4]
    have h1 := hsubopt k hle
    have h2 : Real.sqrt (gap k) ≤ lamOf (xs k) := by
      rw [show lamOf (xs k) = Real.sqrt ((lamOf (xs k)) ^ 2) from (Real.sqrt_sq (hlam0 _)).symm]
      exact Real.sqrt_le_sqrt h1
    rw [hmeasdef]
    exact max_eq_left h2
  -- ## damped phase
  have hdamped : ∀ k, η ≤ meas k → gap (k + 1) ≤ gap k - γ := by
    intro k hk
    have hlamk : η ≤ lamOf (xs k) := by
      by_contra hlt
      push_neg at hlt
      rw [hmeas_eq k hlt] at hk
      linarith
    obtain ⟨t, hbt, hz⟩ := hnxt (xs k) (hxsmem k)
    have hstep := SCBT.step_lower Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α β hα0 hα hβ0 hβ1
      (xs k) (hxsmem k) (Δof (xs k)) (hΔof _ (hxsmem k)) (lamOf (xs k)) (hlam0 _)
      (hlamsq _ (hxsmem k)) t hbt
    have hip : (⟪g (xs k), Δof (xs k)⟫ : ℝ) = -(lamOf (xs k)) ^ 2 := by
      have h := hlamg (xs k) (hxsmem k)
      rw [h]; simp
    have harm := hbt.2.1.2
    rw [hip] at harm
    have hlamk0 : 0 ≤ lamOf (xs k) := hlam0 _
    have h1lam : (0:ℝ) < 1 + lamOf (xs k) := by linarith
    have hdec : α * β * (lamOf (xs k)) ^ 2 / (1 + lamOf (xs k)) ≤ f (xs k) - f (xs k + t • Δof (xs k)) := by
      have hmul : β / (1 + lamOf (xs k)) * (α * (lamOf (xs k)) ^ 2)
          ≤ t * (α * (lamOf (xs k)) ^ 2) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
      have hrw : β / (1 + lamOf (xs k)) * (α * (lamOf (xs k)) ^ 2)
          = α * β * (lamOf (xs k)) ^ 2 / (1 + lamOf (xs k)) := by
        field_simp <;> ring
      rw [hrw] at hmul
      linarith [harm, hmul]
    have hmono : γ ≤ α * β * (lamOf (xs k)) ^ 2 / (1 + lamOf (xs k)) := by
      have h := sq_div_succ_mono hη0.le hlamk
      have hab : (0:ℝ) ≤ α * β := by positivity
      have h2 : α * β * (η ^ 2 / (1 + η)) ≤ α * β * ((lamOf (xs k)) ^ 2 / (1 + lamOf (xs k))) :=
        mul_le_mul_of_nonneg_left h hab
      rw [hγ]
      calc α * β * η ^ 2 / (1 + η) = α * β * (η ^ 2 / (1 + η)) := by ring
        _ ≤ α * β * ((lamOf (xs k)) ^ 2 / (1 + lamOf (xs k))) := h2
        _ = α * β * (lamOf (xs k)) ^ 2 / (1 + lamOf (xs k)) := by ring
    have hnext : xs (k + 1) = xs k + t • Δof (xs k) := by rw [hxssucc k]; exact hz
    simp only [hgapdef, hnext]
    linarith
  -- ## quadratic phase
  set scale : ℝ := 1 / (1 - η) ^ 2 with hscale
  have hscalepos : 0 < scale := by rw [hscale]; positivity
  have hquad : ∀ k, meas k < η → scale * meas (k + 1) ≤ (scale * meas k) ^ 2 := by
    intro k hk
    have hlamk : lamOf (xs k) < η := lt_of_le_of_lt (le_max_left _ _) hk
    have hmk : meas k = lamOf (xs k) := hmeas_eq k hlamk
    obtain ⟨t, hbt, hz⟩ := hnxt (xs k) (hxsmem k)
    have ht1 : t = 1 := SCBT.step_unit Ω hΩo hΩc f hsc g hg H hH hHpd hclosed α β
      hα0 hα hβ0 hβ1 (xs k) (hxsmem k) (Δof (xs k)) (hΔof _ (hxsmem k)) (lamOf (xs k))
      (hlam0 _) (hlamsq _ (hxsmem k)) (by rw [← hη]; exact hlamk.le) t hbt
    have hnext : xs (k + 1) = xs k + Δof (xs k) := by
      rw [hxssucc k, hz, ht1, one_smul]
    have hcontr := ConvexOptimization.sc_newton_decrement_contraction Ω hΩo hΩc f hsc g hg
      H hH hHpd hclosed (xs k) (hxsmem k) (Δof (xs k)) (hΔof _ (hxsmem k))
      (lamOf (xs k)) (hlam0 _) (hlamg _ (hxsmem k)) (by linarith [hη4])
    have hnextmem : xs k + Δof (xs k) ∈ Ω := hcontr.1
    have hlamnext : lamOf (xs (k + 1)) ≤ (lamOf (xs k) / (1 - lamOf (xs k))) ^ 2 := by
      rw [hnext]
      exact hcontr.2 (Δof (xs k + Δof (xs k))) (lamOf (xs k + Δof (xs k)))
        (hΔof _ hnextmem) (hlam0 _) (hlamg _ hnextmem)
    have hden : (0:ℝ) < 1 - lamOf (xs k) := by linarith
    have hbound : lamOf (xs (k + 1)) ≤ scale * (lamOf (xs k)) ^ 2 := by
      have hd2 : (1 - η) ^ 2 ≤ (1 - lamOf (xs k)) ^ 2 :=
        pow_le_pow_left₀ hη1.le (by linarith) 2
      have h1 : (lamOf (xs k) / (1 - lamOf (xs k))) ^ 2
          = (lamOf (xs k)) ^ 2 / (1 - lamOf (xs k)) ^ 2 := div_pow _ _ 2
      have h2 : (lamOf (xs k)) ^ 2 / (1 - lamOf (xs k)) ^ 2 ≤ scale * (lamOf (xs k)) ^ 2 := by
        rw [hscale, div_mul_eq_mul_div, one_mul]
        rcases eq_or_lt_of_le (hlam0 (xs k)) with h | h
        · rw [← h]; simp
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd2
      rw [h1] at hlamnext
      linarith
    have hlamnext_small : lamOf (xs (k + 1)) < η := by
      have h1 : scale * (lamOf (xs k)) ^ 2 ≤ scale * η ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hlam0 _) hlamk.le 2) hscalepos.le
      have h2 : scale * η ^ 2 < η := by
        rw [hscale, div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
        nlinarith only [hη0, hη4, hη1]
      linarith
    have hmk1 : meas (k + 1) = lamOf (xs (k + 1)) := hmeas_eq (k + 1) hlamnext_small
    rw [hmk, hmk1]
    calc scale * lamOf (xs (k + 1)) ≤ scale * (scale * (lamOf (xs k)) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound hscalepos.le
      _ = (scale * lamOf (xs k)) ^ 2 := by ring
  -- ## the counting lemma
  set ε₀ : ℝ := (1 - η) ^ 4 with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hε₀le : ε₀ ≤ 1 := by
    rw [hε₀]
    exact pow_le_one₀ hη1.le (by linarith)
  set ε' : ℝ := min ε (ε₀ / 4) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min hε0 (by positivity)
  have hε'small : ε' ≤ ε₀ / 4 := min_le_right _ _
  have hε'le : ε' ≤ ε := min_le_left _ _
  set K : ℕ := ⌈gap 0 / γ + Real.logb 2 (Real.logb 2 (ε₀ / ε'))⌉₊ with hK
  have hratio : (4:ℝ) ≤ ε₀ / ε' := by
    rw [le_div_iff₀ hε'pos]
    linarith [hε'small]
  have hlogb4 : Real.logb 2 (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow]
    simp
  have hlogb1 : (2:ℝ) ≤ Real.logb 2 (ε₀ / ε') := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 4) hratio
    rwa [hlogb4] at h
  have hlogb2 : (0:ℝ) ≤ Real.logb 2 (Real.logb 2 (ε₀ / ε')) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 2) hlogb1
    rw [show Real.logb 2 (2:ℝ) = 1 by simp] at h
    linarith
  have harg : (0:ℝ) ≤ gap 0 / γ + Real.logb 2 (Real.logb 2 (ε₀ / ε')) := by
    have hq : (0:ℝ) ≤ gap 0 / γ := div_nonneg (hgapnn 0) hγpos.le
    linarith
  have hcount := ConvexOptimization.two_phase_iteration_count_of_suboptimality
    gap meas (1/2) γ scale η ε₀ ε' (by norm_num) hγpos hscalepos hη0 hε₀pos hε'pos
    hε'small
    (by
      have hne : (1 - η) ≠ 0 := ne_of_gt hη1
      rw [hε₀, hscale]; field_simp <;> ring)
    (by
      rw [hscale, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith only [hη0, hη4, hη1])
    hgapnn hmeasnn hdamped hquad
    (by
      intro k
      rw [show (2:ℝ) * (1/2) = 1 by norm_num, div_one]
      exact hsub k)
    K (Nat.le_ceil _)
  refine ⟨xs, K, hxs0, hrun, ?_, ?_⟩
  · -- the iteration count
    have hceil : (K : ℝ) < gap 0 / γ + Real.logb 2 (Real.logb 2 (ε₀ / ε')) + 1 := by
      rw [hK]; exact Nat.ceil_lt_add_one harg
    have hlogmono : Real.logb 2 (Real.logb 2 (ε₀ / ε')) ≤ Real.logb 2 (Real.logb 2 (1 / ε)) := by
      rcases le_or_gt ε (ε₀ / 4) with hcase | hcase
      · have hε'eq : ε' = ε := min_eq_left hcase
        rw [hε'eq]
        have h1 : ε₀ / ε ≤ 1 / ε := by gcongr
        have h2 : Real.logb 2 (ε₀ / ε) ≤ Real.logb 2 (1 / ε) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
        have h3 : (0:ℝ) < Real.logb 2 (ε₀ / ε) := by
          have hh := hlogb1; rw [hε'eq] at hh; linarith
        exact Real.logb_le_logb_of_le (by norm_num) h3 h2
      · have hε'eq : ε' = ε₀ / 4 := min_eq_right hcase.le
        rw [hε'eq]
        have h4 : ε₀ / (ε₀ / 4) = 4 := by field_simp
        rw [h4, hlogb4]
        have hinv : (4:ℝ) ≤ 1 / ε := by
          rw [le_div_iff₀ hε0]; linarith
        have hh5 : (2:ℝ) ≤ Real.logb 2 (1 / ε) := by
          have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 4) hinv
          rwa [hlogb4] at h
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hh5
    have hgamma : gap 0 / γ = (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) * (f x0 - f xstar) := by
      have hg0 : gap 0 = f x0 - f xstar := rfl
      have hpos1 : (0:ℝ) < α * β * (1 - 2 * α) ^ 2 :=
        mul_pos (mul_pos hα0 hβ0) (pow_pos (by linarith) 2)
      rw [hg0, hγeq, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
    rw [← hgamma]
    linarith
  · exact le_trans hcount hε'le

end SCIT


-- ## The barrier method (B&V 11.5)

namespace SCBAR

variable {n : ℕ}

/-- `u - u²/2 ≤ log (1 + u)` for `u ≥ 0`. -/
theorem log_lower_quad {u : ℝ} (hu : 0 ≤ u) : u - u ^ 2 / 2 ≤ Real.log (1 + u) := by
  set ψ : ℝ → ℝ := fun r => Real.log (1 + r) - r + r ^ 2 / 2 with hψ
  have hden : ∀ r ∈ Set.Icc (0:ℝ) u, (0:ℝ) < 1 + r := by
    intro r hr; linarith [hr.1]
  have hd : ∀ r ∈ Set.Icc (0:ℝ) u, HasDerivAt ψ (r ^ 2 / (1 + r)) r := by
    intro r hr
    have hr1 : (0:ℝ) < 1 + r := hden r hr
    have hlin : HasDerivAt (fun s : ℝ => 1 + s) 1 r := by
      simpa using (hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + r)) r :=
      hlin.log (ne_of_gt hr1)
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (2 * r / 2) r := by
      simpa using (hasDerivAt_pow 2 r).div_const 2
    have h := (hlog.sub (hasDerivAt_id r)).add hsq
    refine h.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn ψ (Set.Icc (0:ℝ) u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) ?_ ?_ ?_
    · intro r hr; exact ((hd r hr).continuousAt).continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact ((hd r (Set.mem_Icc_of_Ioo hr)).differentiableAt).differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hrI : r ∈ Set.Icc (0:ℝ) u := Set.mem_Icc_of_Ioo hr
      rw [(hd r hrI).deriv]
      have := hden r hrI
      positivity
  have h := hmono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  have h0 : ψ 0 = 0 := by rw [hψ]; norm_num
  have hu' : ψ u = Real.log (1 + u) - u + u ^ 2 / 2 := rfl
  rw [h0, hu'] at h
  linarith

/-- `u log 2 ≤ log (1 + u)` on `[0,1]`, by concavity of `log`. -/
theorem log_two_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    u * Real.log 2 ≤ Real.log (1 + u) := by
  have hcon : ConcaveOn ℝ (Set.Ioi (0:ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h := hcon.2 (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 1))
    (Set.mem_Ioi.mpr (by norm_num : (0:ℝ) < 2)) (by linarith : (0:ℝ) ≤ 1 - u) h0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rw [show (1 - u) * 1 + u * 2 = 1 + u by ring] at h
  exact h

/-- The outer schedule `μ = 1 + 1/√m` drives the duality gap `m/t` below `ε`
in `⌈√m log₂(m/(t₀ε))⌉` steps. -/
theorem schedule (m t0 ε : ℝ) (hm1 : 1 ≤ m) (ht0 : 0 < t0) (hε : 0 < ε) :
    m / ((1 + 1 / Real.sqrt m) ^
      ⌈Real.sqrt m * Real.logb 2 (m / (t0 * ε))⌉₊ * t0) ≤ ε := by
  have hmpos : (0:ℝ) < m := by linarith
  set sq : ℝ := Real.sqrt m with hsq
  have hsqpos : 0 < sq := Real.sqrt_pos.mpr hmpos
  have hsq1 : 1 ≤ sq := by
    rw [hsq, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hm1
  have hsq2 : sq ^ 2 = m := Real.sq_sqrt hmpos.le
  set μ : ℝ := 1 + 1 / sq with hμ
  have hμ1 : 1 < μ := by rw [hμ]; have : 0 < 1 / sq := by positivity
                         linarith
  have hμpos : (0:ℝ) < μ := by linarith
  set N : ℕ := ⌈sq * Real.logb 2 (m / (t0 * ε))⌉₊ with hN
  have hpowpos : (0:ℝ) < μ ^ N := by positivity
  set R : ℝ := m / (t0 * ε) with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hkey : R ≤ μ ^ N := by
    rcases le_or_gt R 1 with hR1 | hR1
    · calc R ≤ 1 := hR1
        _ ≤ μ ^ N := one_le_pow₀ hμ1.le
    · -- `log R > 0`
      have hlogR : 0 < Real.log R := Real.log_pos hR1
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      -- `√m · log μ ≥ log 2`
      have hu : 1 / sq ≤ 1 := by
        rw [div_le_one hsqpos]; exact hsq1
      have hlogμ : (1 / sq) * Real.log 2 ≤ Real.log μ :=
        log_two_bound (by positivity) hu
      have hsqlogμ : Real.log 2 ≤ sq * Real.log μ := by
        have h := mul_le_mul_of_nonneg_left hlogμ hsqpos.le
        rw [show sq * ((1 / sq) * Real.log 2) = Real.log 2 by field_simp] at h
        linarith
      -- `N ≥ √m logb 2 R`
      have hNge : sq * Real.logb 2 R ≤ (N : ℝ) := by rw [hN, hR]; exact Nat.le_ceil _
      have hlogbR : Real.logb 2 R = Real.log R / Real.log 2 := rfl
      have hNlog : Real.log R ≤ (N : ℝ) * Real.log μ := by
        have h1 : sq * (Real.log R / Real.log 2) ≤ (N : ℝ) := by rw [← hlogbR]; exact hNge
        have h2 : Real.log R / Real.log 2 * (Real.log 2) ≤ (N : ℝ) * Real.log μ := by
          calc Real.log R / Real.log 2 * Real.log 2
              ≤ Real.log R / Real.log 2 * (sq * Real.log μ) := by
                apply mul_le_mul_of_nonneg_left hsqlogμ
                positivity
            _ = (sq * (Real.log R / Real.log 2)) * Real.log μ := by ring
            _ ≤ (N : ℝ) * Real.log μ := by
                apply mul_le_mul_of_nonneg_right h1
                have := Real.log_pos hμ1
                linarith
        rwa [div_mul_cancel₀ _ (ne_of_gt hlog2)] at h2
      have hexp : R ≤ μ ^ N := by
        have hlogpow : Real.log (μ ^ N) = (N : ℝ) * Real.log μ := by rw [Real.log_pow]
        have h := Real.exp_le_exp.mpr (hlogpow ▸ hNlog)
        rwa [Real.exp_log hRpos, Real.exp_log hpowpos] at h
      exact hexp
  rw [div_le_iff₀ (by positivity)]
  have h1 : m = R * (t0 * ε) := by rw [hR]; field_simp
  rw [h1]
  have h2 : R * (t0 * ε) ≤ μ ^ N * (t0 * ε) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  calc R * (t0 * ε) ≤ μ ^ N * (t0 * ε) := h2
    _ = ε * (μ ^ N * t0) := by ring

/-- **B&V §11.5**: the barrier method with the outer schedule `μ = 1 + 1/√m` and a
domain-confined inner line search. -/
theorem barrier_complexity {mI : ℕ} (hmI : 0 < mI)
    (α β t0 ε εnt : ℝ)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht0 : 0 < t0) (hε : 0 < ε) (hεnt0 : 0 < εnt) (hεnt : εnt < 1 / 4)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hf₀_diff : Differentiable ℝ f₀) (hfc_diff : ∀ i, Differentiable ℝ (fc i))
    (hSC : ∀ t : ℝ, 0 ≤ t →
      IsSelfConcordantOn {x | ∀ i, fc i x < 0}
        (fun x => t * f₀ x + logBarrier fc x))
    (hclosed : ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      IsClosed {x | (∀ i, fc i x < 0) ∧ t * f₀ x + logBarrier fc x ≤ c})
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasGradientAt (fun y => t * f₀ y + logBarrier fc y) (g t x) x)
    (H : ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasFDerivAt (g t) (H t x) x)
    (hHpd : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      ∀ v, v ≠ 0 → 0 < ⟪H t x v, v⟫)
    (xc : ℝ → EuclideanSpace ℝ (Fin n))
    (hxc_str : ∀ t : ℝ, 0 < t → ∀ i, fc i (xc t) < 0)
    (hxc_min : ∀ t : ℝ, 0 < t →
      IsMinOn (fun x => t * f₀ x + logBarrier fc x) {x | ∀ i, fc i x < 0} (xc t)) :
    ∃ (w : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (K : ℕ → ℕ),
      (∀ i, w i 0 = xc ((1 + 1 / Real.sqrt mI) ^ i * t0)) ∧
      (∀ i, IsDampedNewtonRunOn {x | ∀ i', fc i' x < 0}
        (fun x => (1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ x + logBarrier fc x)
        (g ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))
        (H ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) α β (w i)) ∧
      (∀ i, ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ (w i (K i)) +
          logBarrier fc (w i (K i))) -
        ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 *
            f₀ (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) +
          logBarrier fc (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))) ≤ εnt) ∧
      (∀ i, (K i : ℝ) ≤
        (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) / 2 +
          Real.logb 2 (Real.logb 2 (1 / εnt)) + 2) ∧
      (mI : ℝ) / ((1 + 1 / Real.sqrt mI) ^
          ⌈Real.sqrt mI * Real.logb 2 (mI / (t0 * ε))⌉₊ * t0) ≤ ε := by
  classical
  set m : ℝ := (mI : ℝ) with hm
  have hm1 : (1:ℝ) ≤ m := by rw [hm]; exact_mod_cast hmI
  have hmpos : (0:ℝ) < m := by linarith
  set sq : ℝ := Real.sqrt m with hsqdef
  have hsqpos : 0 < sq := Real.sqrt_pos.mpr hmpos
  have hsq1 : 1 ≤ sq := by
    rw [hsqdef, show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hm1
  have hsq2 : sq ^ 2 = m := Real.sq_sqrt hmpos.le
  set μ : ℝ := 1 + 1 / sq with hμdef
  have hμ1 : 1 < μ := by
    have : 0 < 1 / sq := by positivity
    rw [hμdef]; linarith
  have hμpos : (0:ℝ) < μ := by linarith
  set Feas : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, fc i x < 0} with hFeasdef
  have hFeasOpen : IsOpen Feas := by
    have hre : Feas = ⋂ i, (fc i) ⁻¹' (Set.Iio 0) := by
      rw [hFeasdef]; ext x; simp
    rw [hre]
    exact isOpen_iInter_of_finite
      (fun i => ((hfc_diff i).continuous).isOpen_preimage _ isOpen_Iio)
  have hFeasConv : Convex ℝ Feas := by
    intro a ha b hb p q hp hq hpq
    intro i
    have ha' : fc i a < 0 := ha i
    have hb' : fc i b < 0 := hb i
    have h := (hfc i).2 (Set.mem_univ a) (Set.mem_univ b) hp hq hpq
    simp only [smul_eq_mul] at h
    have hlt : p * fc i a + q * fc i b < 0 := by
      rcases lt_or_ge 0 p with hp0 | hp0
      · have h1 : p * fc i a < 0 := mul_neg_of_pos_of_neg hp0 ha'
        have h2 : q * fc i b ≤ 0 := by nlinarith only [hq, hb']
        linarith
      · have hp0' : p = 0 := le_antisymm hp0 hp
        have hq1 : q = 1 := by rw [hp0'] at hpq; linarith
        rw [hp0', hq1]
        simpa using hb'
    linarith
  have hτpos : ∀ i : ℕ, (0:ℝ) < μ ^ i * t0 := fun i => by positivity
  -- ## one outer iteration
  have hstep : ∀ i : ℕ, ∃ (wi : ℕ → EuclideanSpace ℝ (Fin n)) (Ki : ℕ),
      wi 0 = xc (μ ^ i * t0) ∧
      IsDampedNewtonRunOn Feas (fun x => μ ^ (i + 1) * t0 * f₀ x + logBarrier fc x)
        (g (μ ^ (i + 1) * t0)) (H (μ ^ (i + 1) * t0)) α β wi ∧
      (Ki : ℝ) ≤ (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) *
        ((μ ^ (i + 1) * t0 * f₀ (xc (μ ^ i * t0)) + logBarrier fc (xc (μ ^ i * t0))) -
          (μ ^ (i + 1) * t0 * f₀ (xc (μ ^ (i + 1) * t0)) +
            logBarrier fc (xc (μ ^ (i + 1) * t0)))) +
        Real.logb 2 (Real.logb 2 (1 / εnt)) + 1 ∧
      ((μ ^ (i + 1) * t0 * f₀ (wi Ki) + logBarrier fc (wi Ki)) -
        (μ ^ (i + 1) * t0 * f₀ (xc (μ ^ (i + 1) * t0)) +
          logBarrier fc (xc (μ ^ (i + 1) * t0)))) ≤ εnt := by
    intro i
    exact SCIT.iteration_bound α β εnt hα0 hα hβ0 hβ1 hεnt0 hεnt Feas hFeasOpen hFeasConv
      (fun x => μ ^ (i + 1) * t0 * f₀ x + logBarrier fc x) (hSC _ (hτpos (i + 1)).le)
      (g (μ ^ (i + 1) * t0)) (fun x hx => hg _ (hτpos (i + 1)) x hx)
      (H (μ ^ (i + 1) * t0)) (fun x hx => hH _ (hτpos (i + 1)) x hx)
      (fun x hx v hv => hHpd _ (hτpos (i + 1)) x hx v hv)
      (xc (μ ^ (i + 1) * t0)) (hxc_str _ (hτpos (i + 1))) (hxc_min _ (hτpos (i + 1)))
      (xc (μ ^ i * t0)) (hxc_str _ (hτpos i)) (fun c => hclosed _ (hτpos (i + 1)) c)
  choose w K hw0 hwrun hwK hwgap using hstep
  -- ## the inherited objective gap is at most `1/2`
  have hgapbd : ∀ i : ℕ,
      (μ ^ (i + 1) * t0 * f₀ (xc (μ ^ i * t0)) + logBarrier fc (xc (μ ^ i * t0))) -
        (μ ^ (i + 1) * t0 * f₀ (xc (μ ^ (i + 1) * t0)) +
          logBarrier fc (xc (μ ^ (i + 1) * t0))) ≤ 1 / 2 := by
    intro i
    have hsucc : μ ^ (i + 1) * t0 = μ * (μ ^ i * t0) := by ring
    have hb := ConvexOptimization.barrier_centering_potential_gap (μ ^ i * t0) μ
      (hτpos i) hμ1 f₀ hf₀ fc hfc hfc_diff hf₀_diff
      (xc (μ ^ i * t0)) (xc (μ ^ (i + 1) * t0))
      (hxc_str _ (hτpos i)) (hxc_str _ (hτpos (i + 1)))
      (hxc_min _ (hτpos i))
      (by rw [← hsucc]; exact hxc_min _ (hτpos (i + 1)))
    rw [← hsucc] at hb
    have hlog : 1 / sq - (1 / sq) ^ 2 / 2 ≤ Real.log μ := by
      have h := log_lower_quad (u := 1 / sq) (by positivity)
      rwa [← hμdef] at h
    have h1 : μ - 1 = 1 / sq := by rw [hμdef]; ring
    have h2 : (1 / sq) ^ 2 = 1 / m := by rw [div_pow, one_pow, hsq2]
    have h3 : μ - 1 - Real.log μ ≤ (1 / sq) ^ 2 / 2 := by rw [h1]; linarith
    have h4 : m * ((1 / sq) ^ 2 / 2) = 1 / 2 := by
      rw [h2]; field_simp
    have h5 : m * (μ - 1 - Real.log μ) ≤ 1 / 2 := by
      calc m * (μ - 1 - Real.log μ) ≤ m * ((1 / sq) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left h3 hmpos.le
        _ = 1 / 2 := h4
    linarith
  have hcoef : (0:ℝ) ≤ (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) := by
    apply div_nonneg (by linarith)
    have : (0:ℝ) < α * β * (1 - 2 * α) ^ 2 :=
      mul_pos (mul_pos hα0 hβ0) (pow_pos (by linarith) 2)
    linarith
  refine ⟨w, K, hw0, hwrun, hwgap, ?_, ?_⟩
  · intro i
    have h1 := hwK i
    have h2 := mul_le_mul_of_nonneg_left (hgapbd i) hcoef
    linarith
  · exact schedule m t0 ε hm1 ht0 hε

end SCBAR


open SCBAR in
/-- **B&V §11.5**: with the outer schedule `μ = 1 + 1/√m`, every centering step needs at
most `(20-8α)/(αβ(1-2α)²)/2 + log₂log₂(1/εₙₜ) + 2` Newton steps, and
`⌈√m log₂(m/(t₀ε))⌉` outer steps drive the duality gap below `ε`. -/
theorem solution {n mI : ℕ} (hmI : 0 < mI)
    (α β t0 ε εnt : ℝ)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (ht0 : 0 < t0) (hε : 0 < ε) (hεnt0 : 0 < εnt) (hεnt : εnt < 1 / 4)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hf₀_diff : Differentiable ℝ f₀) (hfc_diff : ∀ i, Differentiable ℝ (fc i))
    (hSC : ∀ t : ℝ, 0 ≤ t →
      IsSelfConcordantOn {x | ∀ i, fc i x < 0}
        (fun x => t * f₀ x + logBarrier fc x))
    (hclosed : ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      IsClosed {x | (∀ i, fc i x < 0) ∧ t * f₀ x + logBarrier fc x ≤ c})
    (g : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasGradientAt (fun y => t * f₀ y + logBarrier fc y) (g t x) x)
    (H : ℝ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      HasFDerivAt (g t) (H t x) x)
    (hHpd : ∀ t : ℝ, 0 < t → ∀ x, (∀ i, fc i x < 0) →
      ∀ v, v ≠ 0 → 0 < ⟪H t x v, v⟫)
    (xc : ℝ → EuclideanSpace ℝ (Fin n))
    (hxc_str : ∀ t : ℝ, 0 < t → ∀ i, fc i (xc t) < 0)
    (hxc_min : ∀ t : ℝ, 0 < t →
      IsMinOn (fun x => t * f₀ x + logBarrier fc x) {x | ∀ i, fc i x < 0} (xc t)) :
    ∃ (w : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (K : ℕ → ℕ),
      (∀ i, w i 0 = xc ((1 + 1 / Real.sqrt mI) ^ i * t0)) ∧
      (∀ i, IsDampedNewtonRunOn {x | ∀ i', fc i' x < 0}
        (fun x => (1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ x + logBarrier fc x)
        (g ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))
        (H ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) α β (w i)) ∧
      (∀ i, ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 * f₀ (w i (K i)) +
          logBarrier fc (w i (K i))) -
        ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0 *
            f₀ (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0)) +
          logBarrier fc (xc ((1 + 1 / Real.sqrt mI) ^ (i + 1) * t0))) ≤ εnt) ∧
      (∀ i, (K i : ℝ) ≤
        (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) / 2 +
          Real.logb 2 (Real.logb 2 (1 / εnt)) + 2) ∧
      (mI : ℝ) / ((1 + 1 / Real.sqrt mI) ^
          ⌈Real.sqrt mI * Real.logb 2 (mI / (t0 * ε))⌉₊ * t0) ≤ ε :=
  SCBAR.barrier_complexity hmI α β t0 ε εnt hα0 hα hβ0 hβ1 ht0 hε hεnt0 hεnt
    f₀ hf₀ fc hfc hf₀_diff hfc_diff hSC hclosed g hg H hH hHpd xc hxc_str hxc_min
