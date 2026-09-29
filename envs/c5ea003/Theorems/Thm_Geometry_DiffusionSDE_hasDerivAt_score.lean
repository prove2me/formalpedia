-- Prove2me | Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_score
-- name    : Geometry.DiffusionSDE.hasDerivAt_score
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:13:04.584522+00:00
-- url     : https://prove2.me/theorems/ba158edc-d5eb-4d7e-bce8-3e0328033928
-- title:
--   The Gaussian Stein score.
-- statement:
--   **The Gaussian Stein score.**  `∂ₓ log p(x) = -(x-m)/v` for `N(m,v)`.
--
--   ```lean
--   theorem Geometry.DiffusionSDE.hasDerivAt_score(m v x : ℝ) (hv : v ≠ 0) :
--       HasDerivAt (fun y => Real.log (gaussianDensity m v y)) (-(x - m) / v) x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/DiffusionSDE/ReverseTime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/DiffusionSDE/ReverseTime.lean#L53

-- Thm stub generated from Geometry/DiffusionSDE/ReverseTime.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
import Definitions.Def_Geometry_DiffusionSDE_ReverseTime
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

theorem Geometry.DiffusionSDE.hasDerivAt_score(m v x : ℝ) (hv : v ≠ 0) :
    HasDerivAt (fun y => Real.log (gaussianDensity m v y)) (-(x - m) / v) x := by sorry
