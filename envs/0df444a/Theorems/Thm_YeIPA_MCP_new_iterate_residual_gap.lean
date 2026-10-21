-- Prove2me | Theorems.Thm_YeIPA_MCP_new_iterate_residual_gap
-- name    : YeIPA.MCP.new_iterate_residual_gap
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:51.775036+00:00
-- url     : https://prove2.me/theorems/7e3d36be-11c1-4515-b5cd-d272db62d599
-- title:
--   Lemma 8.28 — $r^+=(1-\alpha\eta)r^k$ and $(x^+)^Ts^+=(x^k)^Ts^k(1-\alpha(1-\gamma))+\alpha^2\eta(1-\eta-\gamma)(n+1)\mu^k$
-- statement:
--   In the setting of Lemma 8.27 (an iterate $(x^k,s^k)>0$ in $\mathbb R^{n+1}\times\mathbb R^{n+1}$, $\eta,\gamma\in(0,1)$, a direction $(d_x,d_s)$ solving (8.42)–(8.43), $r^k=s^k-\psi(x^k)$, $\mu^k=(x^k)^Ts^k/(n+1)$), let $\alpha>0$ be a step size such that
--   $$x^+=x^k+\alpha d_x>0\quad(8.46),\qquad s^+=s^k+\alpha d_s+\psi(x^+)-\psi(x^k)-\alpha\nabla\psi(x^k)d_x\quad(8.47),$$
--   and let $r^+=s^+-\psi(x^+)$. Then
--
--   1. $r^+=(1-\alpha\eta)r^k$;
--   2. $(x^+)^Ts^+=(x^k)^Ts^k\,(1-\alpha(1-\gamma))+\alpha^2\eta(1-\eta-\gamma)(n+1)\mu^k$.
--
--   With $\eta=1-\gamma$ the infeasibility residual and the complementarity gap therefore decrease at exactly the same rate.
--
--   **Formalization Note** $s^+$ is defined by the first line of (8.47). The page prints "(x⁺)s⁺" in (ii); the inner product $(x^+)^Ts^+$ is meant. The standing assumptions of §8.4 (continuity, monotonicity and differentiability of $f$ on $\mathbb R^n_{++}$), $\eta,\gamma\in(0,1)$ (p. 268), $\alpha>0$ and $x^+>0$ ((8.46) is stated with "$>0$") are explicit hypotheses.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 269, Lemma 8.28

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Lemma 8.28 (Ye 1997, p. 269). Under the hypotheses of Lemma 8.27, let `α > 0` be a step
size with `x⁺ = xᵏ + αd_x > 0` (8.46), let `s⁺` be given by (8.47), and `r⁺ = s⁺ − ψ(x⁺)`.
Then (i) `r⁺ = (1 − αη)rᵏ` and (ii)
`(x⁺)ᵀs⁺ = (xᵏ)ᵀsᵏ(1 − α(1 − γ)) + α²η(1 − η − γ)(n + 1)μᵏ`. -/
theorem new_iterate_residual_gap {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (η γ : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (x s dx ds : Fin (n + 1) → ℝ) (hx : x ∈ posOrthant (n + 1)) (hs : s ∈ posOrthant (n + 1))
    (hdir : IsDirection f η γ x s dx ds)
    (α : ℝ) (hα : 0 < α) (hxplus : newX x dx α ∈ posOrthant (n + 1)) :
    newS f x s dx ds α - psi f (newX x dx α) = (1 - α * η) • residual f x s ∧
    newX x dx α ⬝ᵥ newS f x s dx ds α =
      (x ⬝ᵥ s) * (1 - α * (1 - γ)) +
        α ^ 2 * η * (1 - η - γ) * ((n : ℝ) + 1) * mu x s := by sorry

end YeIPA.MCP
