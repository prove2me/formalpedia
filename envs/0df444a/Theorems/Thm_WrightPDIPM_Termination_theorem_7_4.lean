-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_theorem_7_4
-- name    : WrightPDIPM.Termination.theorem_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:11.933979+00:00
-- url     : https://prove2.me/theorems/8732d142-7812-4fd4-b455-179edcaa8204
-- title:
--   Theorem 7.4 — the affine-scaling step satisfies ‖(Δx, Δs)‖ ≤ C₅μ in N₋∞(γ), with C₅ uniform
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$ (no rank assumption) and $\gamma \in (0,1)$. Then there is a constant $C_5$ such that for every $(x,\lambda,s) \in \mathcal N_{-\infty}(\gamma)$ and every affine-scaling direction $(\Delta x, \Delta\lambda, \Delta s)$ at it, i.e. a solution of
--   $$A^{\mathsf T}\Delta\lambda + \Delta s = 0,\qquad A\Delta x = 0,\qquad S\Delta x + X\Delta s = -XSe,$$
--   we have
--   $$\|(\Delta x, \Delta s)\| \le C_5\,\mu,\qquad \mu = x^{\mathsf T}s/n.$$
--
--   The affine-scaling step is therefore of the size of the duality measure throughout the wide neighborhood, the key estimate behind the superlinear convergence of Chapter 7.
--
--   **Formalization Note** $C_5$ is chosen before the point and the direction; it depends only on $A, b, c, \gamma$ (a constant chosen after the point would make the statement trivial). The book's proof builds $C_5$ from $C_4$ of Lemma 7.1 and the constants $\hat C_1$, $\hat C_2$ of Lemma 7.2, which have no closed form, so $C_5$ stays existential. No full-row-rank hypothesis is added: the printed statement has none. Norms are Euclidean; $\|(\Delta x,\Delta s)\| = (\|\Delta x\|^2 + \|\Delta s\|^2)^{1/2}$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 133, Theorem 7.4

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Theorem 7.4 (p. 133): for `γ ∈ (0, 1)` there is a constant `C₅`, chosen before the point
(it depends only on `A, b, c, γ`), such that for every `(x, λ, s) ∈ N_{-∞}(γ)` and every
affine-scaling direction `(Δx, Δλ, Δs)` from (7.1), `‖(Δx, Δs)‖ ≤ C₅μ`. -/
theorem theorem_7_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C₅ : ℝ, ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c γ →
        ∀ (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ),
          IsAffineStep A x s dx dlam ds → norm2Pair dx ds ≤ C₅ * mu x s := by sorry

end WrightPDIPM.Termination
