-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_7_6
-- name    : WrightPDIPM.Termination.lemma_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:27.006882+00:00
-- url     : https://prove2.me/theorems/61f14504-698f-40e6-90b5-7b65a1feda34
-- title:
--   Lemma 7.6 — from N₂(0.25), the affine-scaling step to the boundary of N₂(0.5) has α ≥ 1 − 4C₅²μ
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and let $C_5$ be a constant of Theorem 7.4 for $\gamma = 0.5$: $\|(\Delta x,\Delta s)\| \le C_5\mu$ for every point of $\mathcal N_{-\infty}(0.5)$ and every affine-scaling direction at it. Suppose $(x,\lambda,s) \in \mathcal N_2(0.25)$ and $(\Delta x,\Delta\lambda,\Delta s)$ is an affine-scaling direction at it, and write $(x(\alpha),\lambda(\alpha),s(\alpha)) = (x,\lambda,s) + \alpha(\Delta x,\Delta\lambda,\Delta s)$. Then $(x(\alpha),\lambda(\alpha),s(\alpha)) \in \mathcal N_2(0.5)$ for every $\alpha \in [0, 1 - 4C_5^2\mu]$; consequently, if $\alpha$ is the largest value in $[0,1]$ for which $(x(\alpha),\lambda(\alpha),s(\alpha)) \in \mathcal N_2(0.5)$, then
--   $$\alpha \ge 1 - 4C_5^2\mu.$$
--
--   The predictor step of the predictor-corrector method thus approaches length one as $\mu \to 0$, which gives its two-step quadratic convergence (Theorem 7.7).
--
--   **Formalization Note** "$C_5$ is defined from Theorem 7.4 with $\gamma = 0.5$" is a hypothesis on $C_5$: the uniform bound of Theorem 7.4 at $\gamma = 0.5$. "The largest value of $\alpha$" need not exist in general, so the statement is: every $\alpha$ in $[0, 1 - 4C_5^2\mu]$ is admissible (what the proof shows), and any greatest admissible $\alpha \in [0,1]$ satisfies (7.17). Norms are Euclidean.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 135, Lemma 7.6

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma 7.6 (p. 135): let `C₅` be a constant of Theorem 7.4 for `γ = 0.5`, i.e.
`‖(Δx, Δs)‖ ≤ C₅μ` for every point of `N_{-∞}(0.5)` and every affine-scaling direction there.
If `(x, λ, s) ∈ N₂(0.25)` and `(Δx, Δλ, Δs)` solves (7.1), then
`(x(α), λ(α), s(α)) = (x, λ, s) + α(Δx, Δλ, Δs) ∈ N₂(0.5)` for every `α ∈ [0, 1 − 4C₅²μ]`, and
hence any largest `α ∈ [0, 1]` with `(x(α), λ(α), s(α)) ∈ N₂(0.5)` satisfies
`α ≥ 1 − 4C₅²μ` (7.17). -/
theorem lemma_7_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (C₅ : ℝ)
    (hC₅ : ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c (1 / 2) →
        ∀ (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ),
          IsAffineStep A x s dx dlam ds → norm2Pair dx ds ≤ C₅ * mu x s)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c (1 / 4))
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsAffineStep A x s dx dlam ds) :
    (∀ α ∈ Set.Icc (0 : ℝ) (1 - 4 * C₅ ^ 2 * mu x s),
        (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2)) ∧
      ∀ αk : ℝ, IsGreatest {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
          (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} αk →
        1 - 4 * C₅ ^ 2 * mu x s ≤ αk := by sorry

end WrightPDIPM.Termination
