-- Prove2me | Definitions.Def_Geometry_DiffusionSDE_ReverseTime
-- name    : Geometry_DiffusionSDE_ReverseTime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:13:12.15966+00:00
-- url     : https://prove2.me/theorems/df74331b-994c-4f1b-924e-1878b231bb41
-- title:
--   Aether Catalog definitions — Geometry_DiffusionSDE_ReverseTime
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.DiffusionSDE.ReverseTime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/DiffusionSDE/ReverseTime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
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


namespace Geometry.DiffusionSDE


/-- **Anderson's reverse-time drift** `b(x) = θx - σ²(x-m(s))/v(s) = -f(x) + σ²·score`. -/
noncomputable def reverseDrift (θ σ2 m0 v0 s y : ℝ) : ℝ :=
  θ * y - σ2 * (y - ouMean θ m0 s) / ouVar θ σ2 v0 s




end Geometry.DiffusionSDE


