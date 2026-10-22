-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_10
-- name    : WrightPDIPM.PathFollowing.lemma_5_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:00.8909+00:00
-- url     : https://prove2.me/theorems/ccc4a43c-0534-45d7-b705-059f8f48dfca
-- title:
--   Lemma 5.10 — ‖ΔXΔSe‖ ≤ 2^{−3/2}(1 + 1/γ)nμ in N₋∞(γ)
-- statement:
--   Let $A, b, c$ be LP data, $\gamma \in (0,1)$ and $\sigma \in [0,1]$. Suppose $(x,\lambda,s) \in \mathcal N_{-\infty}(\gamma)$, that is, $(x,\lambda,s)$ is strictly feasible and $x_i s_i \ge \gamma\mu$ for every $i$, with $\mu = x^{\mathsf T}s/n$, and let $(\Delta x,\Delta\lambda,\Delta s)$ solve the step equations (1.12) at this point with centering parameter $\sigma$. Then
--   $$\|\Delta X \Delta S e\|_2 \le 2^{-3/2}\Bigl(1 + \frac1\gamma\Bigr) n\mu .$$
--
--   This is the analogue of Lemma 5.4 for the wide neighborhood; the extra factor $n$ is what separates the $O(n\log(1/\epsilon))$ bound of the long-step method from the $O(\sqrt n\log(1/\epsilon))$ bound of the short-step one.
--
--   **Formalization Note** The page gives no range for $\gamma$ and $\sigma$ in this lemma; the standing ranges $\gamma \in (0,1)$ of (1.16) and $\sigma \in [0,1]$ of (1.12) are stated as hypotheses.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 98, Lemma 5.10

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.10 (p. 98): if `(x, λ, s) ∈ N_{-∞}(γ)` and `(Δx, Δλ, Δs)` solves (1.12) with
centering parameter σ, then `‖ΔXΔSe‖ ≤ 2^{−3/2}(1 + 1/γ)nμ`. γ ∈ (0, 1) (from (1.16)) and
σ ∈ [0, 1] (from (1.12)) are the book's standing ranges. -/
theorem lemma_5_10 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ σ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ NegInf A b c γ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) :
    norm2 (fun i => dx i * ds i) ≤
      (2 : ℝ) ^ (-((3 : ℝ) / 2)) * (1 + 1 / γ) * (n : ℝ) * mu x s := by sorry

end WrightPDIPM.PathFollowing
