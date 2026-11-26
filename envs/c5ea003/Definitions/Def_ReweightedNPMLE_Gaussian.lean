-- Prove2me | Definitions.Def_ReweightedNPMLE_Gaussian
-- name    : ReweightedNPMLE_Gaussian
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:15:04.549249+00:00
-- url     : https://prove2.me/theorems/7db2e116-d756-41fc-8218-ab9fa0a3d2ce
-- title:
--   Gaussian location kernels, scores, and finite signed mixtures
-- statement:
--   The ambient space is \(\mathbb R^d\) with its Euclidean norm. Define
--   \[
--   c_d=(2\pi)^{-d/2},\quad
--   \phi_d(x)=c_de^{-\|x\|^2/2},\quad
--   k_d(x,\theta)=c_de^{-\|x-\theta\|^2/2},
--   \quad s(x,\theta)=\langle x,\theta\rangle-\|\theta\|^2/2.
--   \]
--   For a finite family of real coefficients \(w_i\) and locations \(\theta_i\), the signed mixture is \(f_{w,\theta}(x)=\sum_iw_i k_d(x,\theta_i)\). Probability mixtures impose \(w_i\ge0\) and \(\sum_iw_i=1\). The normalization makes \(\phi_d\) integrable with integral one; the centered density and location kernel are continuous and strictly positive. The score isolates the parameter-dependent exponential after factoring out the centered density.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Gaussian.lean#L20-L143

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE

/-- The ambient Euclidean parameter and observation space. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The exponent remaining after the common centered Gaussian factor is removed. -/
noncomputable def gaussianScore {d : ℕ} (x θ : Point d) : ℝ :=
  inner ℝ x θ - ‖θ‖ ^ 2 / 2

/-- The standard Gaussian normalizing constant in dimension `d`. -/
noncomputable def gaussianConstant (d : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2)

/-- The standard centered Gaussian density. -/
noncomputable def gaussianDensity (d : ℕ) (x : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2)

/-- The standard Gaussian location kernel. -/
noncomputable def gaussianKernel (d : ℕ) (x θ : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x - θ‖ ^ 2 / 2)

/-- A finitely supported signed Gaussian mixture.  Probability mixtures are
obtained by imposing nonnegative weights with total mass one. -/
noncomputable def finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) (x : Point d) : ℝ :=
  ∑ i, w i * gaussianKernel d x (θ i)

theorem gaussianConstant_pos (d : ℕ) : 0 < gaussianConstant d := by
  unfold gaussianConstant
  positivity

theorem gaussianDensity_pos (d : ℕ) (x : Point d) : 0 < gaussianDensity d x := by
  unfold gaussianDensity
  exact mul_pos (gaussianConstant_pos d) (Real.exp_pos _)

theorem gaussianKernel_pos (d : ℕ) (x θ : Point d) : 0 < gaussianKernel d x θ := by
  unfold gaussianKernel
  exact mul_pos (gaussianConstant_pos d) (Real.exp_pos _)



theorem continuous_gaussianDensity (d : ℕ) : Continuous (gaussianDensity d) := by
  unfold gaussianDensity
  fun_prop

theorem continuous_gaussianKernel (d : ℕ) :
    Continuous fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2 := by
  unfold gaussianKernel
  fun_prop









/-- The centered multivariate Gaussian density is Bochner integrable. -/
theorem gaussianDensity_integrable (d : ℕ) : Integrable (gaussianDensity d) := by
  change Integrable (fun x : Point d ↦
    gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2))
  apply Integrable.const_mul
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (1 / 2 : ℂ)) (by norm_num) 0 0
  have hn := hc.norm
  have heq : (fun x : Point d ↦ Real.exp (-‖x‖ ^ 2 / 2)) =
      fun x ↦ ‖Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 +
        0 * (inner ℝ (0 : Point d) x : ℂ))‖ := by
    funext x
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.zero_im,
      zero_mul, add_zero]
    congr 1
    norm_num
    norm_cast
    ring
  rw [heq]
  exact hn

/-- The normalization chosen in `gaussianConstant` makes the centered
Gaussian density integrate to one in every finite dimension. -/
theorem integral_gaussianDensity (d : ℕ) :
    ∫ x : Point d, gaussianDensity d x = 1 := by
  simp only [gaussianDensity]
  rw [integral_const_mul]
  have hfun : (fun x : Point d ↦ Real.exp (-‖x‖ ^ 2 / 2)) =
      fun x ↦ Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    funext x
    congr 1
    ring
  rw [hfun,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (show (0 : ℝ) < 1 / 2 by norm_num)]
  simp only [gaussianConstant]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  rw [← Real.rpow_add (by positivity : 0 < 2 * Real.pi)]
  rw [finrank_euclideanSpace_fin]
  rw [show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]



























end ReweightedNPMLE


