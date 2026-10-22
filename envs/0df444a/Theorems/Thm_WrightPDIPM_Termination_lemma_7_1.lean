-- Prove2me | Theorems.Thm_WrightPDIPM_Termination_lemma_7_1
-- name    : WrightPDIPM.Termination.lemma_7_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:14.153981+00:00
-- url     : https://prove2.me/theorems/72b76229-90d9-4d8a-85b4-42c19cdafe59
-- title:
--   Lemma 7.1 — the affine-scaling step satisfies ‖Δx_N‖, ‖Δs_B‖ ≤ C₄μ with C₄ = n/(γ^{1/2}C₃)
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, $\gamma \in (0,1)$, let $\mathcal B, \mathcal N$ be the optimal partition and $C_3 = \epsilon(A,b,c)/n$. Suppose $(x,\lambda,s) \in \mathcal N_{-\infty}(\gamma)$ and $(\Delta x, \Delta\lambda, \Delta s)$ is an affine-scaling direction:
--   $$\begin{bmatrix} 0 & A^{\mathsf T} & I \\ A & 0 & 0 \\ S & 0 & X\end{bmatrix}\begin{bmatrix}\Delta x\\ \Delta\lambda\\ \Delta s\end{bmatrix} = \begin{bmatrix} 0 \\ 0 \\ -XSe\end{bmatrix}.$$
--   Then, with $C_4 = n/(\gamma^{1/2}C_3)$,
--   $$\|\Delta x_{\mathcal N}\| \le C_4\mu,\qquad \|\Delta s_{\mathcal B}\| \le C_4\mu.$$
--
--   Half of the components of the affine-scaling step are thus $O(\mu)$, uniformly over the neighborhood; this is the first step towards Theorem 7.4.
--
--   **Formalization Note** The book writes "there is a constant $C_4$"; its proof gives $C_4 = n/(\gamma^{1/2}C_3)$ (7.6) with $C_3 = \epsilon(A,b,c)/n$ (7.4), used explicitly. $\gamma \in (0,1)$ is the range of (1.16). $\|\Delta x_{\mathcal N}\|$ is the Euclidean norm of the subvector indexed by $\mathcal N$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 130, Lemma 7.1 (C₄ from Eq. (7.6), p. 131)

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

namespace WrightPDIPM.Termination

open Matrix

/-- Lemma 7.1 (p. 130): for `γ ∈ (0, 1)`, every `(x, λ, s) ∈ N_{-∞}(γ)` and every affine-scaling
direction `(Δx, Δλ, Δs)` from (7.1) satisfy `‖Δx_N‖ ≤ C₄μ` and `‖Δs_B‖ ≤ C₄μ`, with the
constant `C₄ = n/(γ^{1/2}C₃)` (7.6), `C₃ = ε(A, b, c)/n` (7.4), which does not depend on the
point. -/
theorem lemma_7_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ NegInf A b c γ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsAffineStep A x s dx dlam ds) :
    norm2On (indexN A b c) dx ≤ (n / (Real.sqrt γ * C3 A b c)) * mu x s ∧
      norm2On (indexB A b c) ds ≤ (n / (Real.sqrt γ * C3 A b c)) * mu x s := by sorry

end WrightPDIPM.Termination
