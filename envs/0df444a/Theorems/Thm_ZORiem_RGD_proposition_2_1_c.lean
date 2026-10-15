-- Prove2me | Theorems.Thm_ZORiem_RGD_proposition_2_1_c
-- name    : ZORiem.RGD.proposition_2_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:29.123116+00:00
-- url     : https://prove2.me/theorems/22b7f88a-23ab-478c-87c5-0f606fdb50c0
-- title:
--   Proposition 2.1(c), p. 8 — second moment E‖g_µ(x)‖² ≤ (µ²/2)L²(d+6)³ + 2(d+4)‖grad f(x)‖²
-- statement:
--   In the setting of Proposition 2.1(a) — $M\subseteq E$ a $C^1$ embedded submanifold of dimension $d$, $R$ a global retraction, $f$ differentiable and satisfying Assumption 2.1 with constant $L\ge0$, $x\in M$, $\mu>0$, and $g_\mu(x)$ the zeroth-order estimator (2.5) built from $u_0\sim N(0,I_n)$ — the second moment of the estimator is finite and
--
--   $$\mathbb E_{u_0}\big(\|g_\mu(x)\|^2\big)\le\frac{\mu^2}{2}L^2(d+6)^3+2(d+4)\,\|\operatorname{grad}f(x)\|^2 .$$
--
--   This variance-type bound controls the second-order term of the descent inequality in the analysis of ZO-RGD; the factor $d+4$ is what forces the step size $1/(2(d+4)L)$ of Theorem 3.1.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of $\|g_\mu(x)\|^2$, compared with a finite right-hand side, so the statement also asserts that the second moment is finite. As in (a), "smooth" is weakened to differentiable.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Proposition 2.1(c), p. 8

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_IsRetraction
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ZORiem_RGD_zoGrad

open MeasureTheory ProbabilityTheory ProjLikeRetr.Retractor
open scoped InnerProductSpace

namespace ZORiem.RGD

/-- Proposition 2.1(c), p. 8: under Assumption 2.1, at every `x ∈ M` and for every `µ > 0`, the second
moment of the estimator satisfies `E‖g_µ(x)‖² ≤ (µ²/2)L²(d+6)³ + 2(d+4)‖grad f(x)‖²` (as a lower
Lebesgue integral, so the bound also asserts finiteness). -/
theorem proposition_2_1_c {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Set E) (d : ℕ) (hM : IsSubmanifold 1 d M)
    (R : E → E → E) (hR : IsRetraction M R)
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : 0 ≤ L)
    (hA21 : ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
      |f (R x η) - f x - ⟪rgrad M f x, η⟫_ℝ| ≤ L / 2 * ‖η‖ ^ 2)
    (x : E) (hx : x ∈ M) (mu : ℝ) (hmu : 0 < mu) :
    ∫⁻ u₀, ENNReal.ofReal (‖zoGrad M R f mu x u₀‖ ^ 2) ∂(stdGaussian E) ≤
      ENNReal.ofReal (mu ^ 2 / 2 * L ^ 2 * ((d : ℝ) + 6) ^ 3 + 2 * ((d : ℝ) + 4) * ‖rgrad M f x‖ ^ 2) := by sorry

end ZORiem.RGD
