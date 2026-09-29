-- Prove2me | solution 1 for Geometry.DiffusionSDE.ou_reverse_fokker_planck
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:30:58.820835+00:00
-- url     : https://prove2.me/submissions/927d73c7-c895-4b20-9799-6d6d31a619e2

-- Sol generated from Geometry/DiffusionSDE/ReverseTime.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
import Definitions.Def_Geometry_DiffusionSDE_ReverseTime
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_t
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_x
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_xx
import Theorems.Thm_Geometry_DiffusionSDE_ouMean_hasDerivAt
import Theorems.Thm_Geometry_DiffusionSDE_ouVar_hasDerivAt
/-
# Diffusion Models as SDEs — Part III: The Reverse-Time SDE

This file formalizes the **time reversal** at the heart of score-based diffusion
generative models (Anderson 1982; Song et al. 2021).

If the forward OU process `dX = -θ X dt + σ dW` has marginal densities `p(·,t)`
(solving the Fokker–Planck equation of `FokkerPlanck.lean`), then the *reverse-time*
process `X̄_τ = X_{T-τ}` is again a diffusion, with drift

  b(x,τ) = -f(x) + σ² ∂ₓ log p(x, T-τ) = θ x + σ² · score(x, T-τ),

where `score = ∂ₓ log p` is the Stein score.  Its density `q(x,τ) = p(x, T-τ)`
satisfies the **reverse Fokker–Planck equation**

  ∂_τ q = -∂ₓ(b·q) + (σ²/2) ∂ₓₓ q,

and therefore propagates the (near-)stationary law `q(·,0) = p(·,T)` back to the
**data distribution** `q(·,T) = p(·,0)`.

## Main results

* `hasDerivAt_score`            — the Gaussian Stein score is `∂ₓ log p = -(x-m)/v`.
* `ou_reverse_fokker_planck`    — **`q(x,τ)=p(x,T-τ)` solves the reverse FP PDE**
                                  with Anderson's reverse drift `reverseDrift`.
* `ou_reverse_recovers_data`    — at the terminal reverse time the marginal is the
                                  data density: `q(·,T) = p(·,0)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): reversing time turns the forward FP into another FP
whose drift is corrected by `σ²·score`; the reversed flow recovers `p(·,0)`.
Experiment (Experimenter): differentiate `q(x,τ)=p(x,T-τ)` in τ (chain rule,
`(T-τ)' = -1`) and assemble the reverse FP RHS from the score-corrected drift via
the product rule; reduce to a rational identity by `field_simp; ring`.
Analysis (Analyst): the reverse drift is exactly `b = -f + σ²∂ₓlog p`; the
algebraic miracle is that `-∂ₜp = -∂ₓ(f q) + (σ²/2)∂ₓₓq` rewrites as
`-∂ₓ(b q)+(σ²/2)∂ₓₓq` because `2D∂ₓₓq = 2D∂ₓ(q·∂ₓlog q)`.  The score appears
inside the drift, so the FP RHS gains an extra product-rule term — yet everything
cancels.
Critique (Critic): the theorem uses real `deriv`s and the data-recovery corollary
is a genuine *consequence* of the dynamics (not the whole content); the reverse
PDE needs `v(T-τ)>0` and `θ≠0`, matching the forward result.
Synthesis (PI): closes the diffusion-model SDE triangle: forward OU → Fokker–
Planck → reverse-time recovery, all at the level of verified marginal PDEs.
-- !-- Lab Notes -- !--
-/


open Geometry.DiffusionSDE







open Geometry.DiffusionSDE in
theorem solution(θ σ2 m0 v0 x T τ : ℝ) (hθ : θ ≠ 0)
    (hv : 0 < ouVar θ σ2 v0 (T - τ)) :
    deriv (fun r => ouDensity θ σ2 m0 v0 x (T - r)) τ
      = - deriv (fun y => reverseDrift θ σ2 m0 v0 (T - τ) y * ouDensity θ σ2 m0 v0 y (T - τ)) x
        + (σ2 / 2) * deriv (fun y => deriv (fun z => ouDensity θ σ2 m0 v0 z (T - τ)) y) x := by
  set s := T - τ with hs
  set m := ouMean θ m0 with hm_def
  set v := ouVar θ σ2 v0 with hv_def
  have hvne : v s ≠ 0 := ne_of_gt hv
  have hG : HasDerivAt (fun w => gaussianDensity (m w) (v w) x)
      (gaussianDensity (m s) (v s) x *
        ((x - m s) / v s * (-θ * m s)
          + ((x - m s) ^ 2 - v s) / (2 * (v s) ^ 2) * (-(2 * θ) * v s + σ2))) s :=
    hasDerivAt_gaussian_t m v (-θ * m s) (-(2 * θ) * v s + σ2) x s hv
      (ouMean_hasDerivAt θ m0 s) (ouVar_hasDerivAt θ σ2 v0 s hθ)
  have hφ : HasDerivAt (fun r : ℝ => T - r) (-1) τ := by
    simpa using (hasDerivAt_const τ T).sub (hasDerivAt_id τ)
  have hcomp := hG.comp τ hφ
  have hLd : deriv (fun r => gaussianDensity (m (T - r)) (v (T - r)) x) τ
      = gaussianDensity (m s) (v s) x *
        ((x - m s) / v s * (-θ * m s)
          + ((x - m s) ^ 2 - v s) / (2 * (v s) ^ 2) * (-(2 * θ) * v s + σ2)) * (-1) :=
    hcomp.deriv
  have hL : (fun r => ouDensity θ σ2 m0 v0 x (T - r))
      = fun r => gaussianDensity (m (T - r)) (v (T - r)) x := by funext r; rfl
  rw [hL, hLd]
  have hb : HasDerivAt (fun y => reverseDrift θ σ2 m0 v0 s y) (θ - σ2 / v s) x := by
    unfold reverseDrift
    rw [← hm_def, ← hv_def]
    have h1 : HasDerivAt (fun y : ℝ => θ * y) θ x := by simpa using (hasDerivAt_id x).const_mul θ
    have h2 : HasDerivAt (fun y : ℝ => σ2 * (y - m s) / v s) (σ2 / v s) x := by
      have := (((hasDerivAt_id x).sub_const (m s)).const_mul σ2).div_const (v s)
      simpa using this
    simpa using h1.sub h2
  have hbq : HasDerivAt (fun y => reverseDrift θ σ2 m0 v0 s y * gaussianDensity (m s) (v s) y)
      ((θ - σ2 / v s) * gaussianDensity (m s) (v s) x
        + reverseDrift θ σ2 m0 v0 s x * (gaussianDensity (m s) (v s) x * (-(x - m s) / v s))) x :=
    hb.mul (hasDerivAt_gaussian_x (m s) (v s) x hvne)
  have hRq : (fun y => reverseDrift θ σ2 m0 v0 s y * ouDensity θ σ2 m0 v0 y s)
      = (fun y => reverseDrift θ σ2 m0 v0 s y * gaussianDensity (m s) (v s) y) := by funext y; rfl
  rw [hRq, hbq.deriv]
  have hinner : (fun y => deriv (fun z => ouDensity θ σ2 m0 v0 z s) y)
      = (fun y => gaussianDx (m s) (v s) y) := by
    funext y
    have := (hasDerivAt_gaussian_x (m s) (v s) y hvne).deriv
    simpa [ouDensity, gaussianDx] using this
  rw [hinner, (hasDerivAt_gaussian_xx (m s) (v s) x hvne).deriv]
  unfold reverseDrift
  rw [← hm_def, ← hv_def]
  field_simp
  ring
