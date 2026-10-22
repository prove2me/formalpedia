-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_theorem_5_11
-- name    : WrightPDIPM.PathFollowing.theorem_5_11
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:58.671137+00:00
-- url     : https://prove2.me/theorems/8b7c1485-d80f-4de0-9240-9c84c88a71c4
-- title:
--   Theorem 5.11 — Algorithm LPF has μ_{k+1} ≤ (1 − δ/n)μ_k with the explicit δ of the proof
-- statement:
--   Let $\gamma \in (0,1)$ and $0 < \sigma_{\min} < \sigma_{\max} < 1$ be the parameters of Algorithm LPF, and let $A, b, c$ be LP data of any dimensions $m, n$. Let $(x^k,\lambda^k,s^k)_{k\ge0}$ be a sequence of iterates of Algorithm LPF: $(x^0,\lambda^0,s^0) \in \mathcal N_{-\infty}(\gamma)$; at each $k$, $\sigma_k \in [\sigma_{\min},\sigma_{\max}]$, the direction $(\Delta x^k,\Delta\lambda^k,\Delta s^k)$ solves the step equations (1.12) at the $k$-th iterate with $\sigma_k$, $\alpha_k$ is the largest $\alpha \in [0,1]$ with $(x^k,\lambda^k,s^k) + \alpha(\Delta x^k,\Delta\lambda^k,\Delta s^k) \in \mathcal N_{-\infty}(\gamma)$ (5.21), and $(x^{k+1},\lambda^{k+1},s^{k+1}) = (x^k,\lambda^k,s^k) + \alpha_k(\Delta x^k,\Delta\lambda^k,\Delta s^k)$. Then, with $\mu_k = (x^k)^{\mathsf T}s^k/n$,
--   $$\mu_{k+1} \le \Bigl(1 - \frac{\delta}{n}\Bigr)\mu_k \quad\text{for all } k \ge 0, \qquad \delta = 2^{3/2}\gamma\,\frac{1-\gamma}{1+\gamma}\,\min\{\sigma_{\min}(1-\sigma_{\min}),\ \sigma_{\max}(1-\sigma_{\max})\}.$$
--
--   With the generic complexity theorem this gives the $O(n\log(1/\epsilon))$ iteration bound of the long-step method (Theorem 5.12).
--
--   **Formalization Note** The book states only that some $\delta$ independent of $n$ exists; the statement uses the explicit $\delta$ derived at the end of the proof (p. 100), which depends only on $\gamma, \sigma_{\min}, \sigma_{\max}$ and implies the book's claim. The "largest $\alpha$" of (5.21) is a hypothesis on the chosen $\alpha_k$ (`IsGreatest`), not a construction.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 98, Theorem 5.11; δ from the proof, p. 100; Algorithm LPF, pp. 96–97

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Theorem 5.11 (p. 98), with the explicit constant of its proof (p. 100):
for the parameters γ ∈ (0, 1), 0 < σ_min < σ_max < 1 of Algorithm LPF, every sequence of LPF
iterates satisfies `μ_{k+1} ≤ (1 − δ/n) μ_k` for all k ≥ 0, where
`δ = 2^{3/2} γ ((1 − γ)/(1 + γ)) min{σ_min(1 − σ_min), σ_max(1 − σ_max)}` depends only on
γ, σ_min, σ_max (not on n or the data). -/
theorem theorem_5_11 (γ σmin σmax : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hσmin : 0 < σmin) (hσ : σmin < σmax) (hσmax : σmax < 1)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hLPF : IsLPFIterates A b c γ σmin σmax x lam s σ α dx dlam ds) :
    ∀ k : ℕ, mu (x (k + 1)) (s (k + 1)) ≤
      (1 - (2 : ℝ) ^ ((3 : ℝ) / 2) * γ * ((1 - γ) / (1 + γ)) *
          min (σmin * (1 - σmin)) (σmax * (1 - σmax)) / (n : ℝ)) * mu (x k) (s k) := by sorry

end WrightPDIPM.PathFollowing
