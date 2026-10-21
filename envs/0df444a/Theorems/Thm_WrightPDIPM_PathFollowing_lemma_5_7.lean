-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_7
-- name    : WrightPDIPM.PathFollowing.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:58.552964+00:00
-- url     : https://prove2.me/theorems/45b12da7-9943-4536-995e-92df028c6b64
-- title:
--   Lemma 5.7 — the predictor step from N₂(0.25) stays in N₂(0.5) for α ∈ [0, ᾱ]
-- statement:
--   Let $A, b, c$ be LP data, let $(x,\lambda,s) \in \mathcal N_2(0.25)$, and let $(\Delta x, \Delta\lambda, \Delta s)$ solve the step equations (1.12) at this point with $\sigma = 0$ (the predictor, or affine-scaling, direction). Put
--   $$\bar\alpha = \min\Bigl(\frac12, \Bigl(\frac{\mu}{8\|\Delta X\Delta S e\|_2}\Bigr)^{1/2}\Bigr), \qquad (5.19)$$
--   with $\bar\alpha = \tfrac12$ when $\Delta X \Delta S e = 0$. Then:
--
--   1. $(x,\lambda,s) + \alpha(\Delta x,\Delta\lambda,\Delta s) \in \mathcal N_2(0.5)$ for every $\alpha \in [0, \bar\alpha]$;
--   2. if $\alpha_k$ is the largest $\alpha \in [0,1]$ with $(x,\lambda,s) + \alpha(\Delta x,\Delta\lambda,\Delta s) \in \mathcal N_2(0.5)$ — the predictor step length of Algorithm PC (5.18) — then $\alpha_k \ge \bar\alpha$ and $\mu(\alpha_k) \le (1-\bar\alpha)\mu$, where $\mu(\alpha) = (x + \alpha\Delta x)^{\mathsf T}(s + \alpha\Delta s)/n$.
--
--   This is the step-length estimate behind the $O(\sqrt n\log(1/\epsilon))$ complexity of the predictor-corrector method.
--
--   **Formalization Note** When $\Delta X\Delta S e = 0$ the ratio in (5.19) is read as $+\infty$, so $\bar\alpha = 1/2$; the definition splits this case off, because real division by zero would make $\bar\alpha = 0$ and the first claim trivial. Part 2 is stated for any $\alpha_k$ that is the greatest element of the admissible set (`IsGreatest`); it does not assert that such a largest value exists.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 94, Lemma 5.7, Eq. (5.19); p. 93, Algorithm PC, Eq. (5.18)

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.7 (p. 94): if `(x, λ, s) ∈ N₂(0.25)` and `(Δx, Δλ, Δs)` solves (1.12) with σ = 0,
then `(x(α), λ(α), s(α)) ∈ N₂(0.5)` for all α ∈ [0, ᾱ], with ᾱ as in (5.19) (`alphaBar`,
equal to 1/2 when ΔXΔSe = 0). Hence the predictor step of Algorithm PC — any α_k that is the
largest α ∈ [0, 1] with `(x(α), λ(α), s(α)) ∈ N₂(0.5)` (5.18) — has length at least ᾱ, and the
new value of μ is at most (1 − ᾱ)μ. -/
theorem lemma_5_7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c (1 / 4))
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s 0 dx dlam ds) :
    (∀ α ∈ Set.Icc (0 : ℝ) (alphaBar x s dx ds),
        (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2)) ∧
      ∀ αk : ℝ, IsGreatest {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
          (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} αk →
        alphaBar x s dx ds ≤ αk ∧
          mu (x + αk • dx) (s + αk • ds) ≤ (1 - alphaBar x s dx ds) * mu x s := by sorry

end WrightPDIPM.PathFollowing
