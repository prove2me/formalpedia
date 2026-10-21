-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_lemma_6_6
-- name    : WrightPDIPM.Infeasible.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:59.271784+00:00
-- url     : https://prove2.me/theorems/7bbae2fb-ef46-403a-a5f5-aa159d7a5866
-- title:
--   Lemma 6.6 — ‖(D^k)⁻¹Δx^k‖, ‖D^kΔs^k‖ ≤ ωnμ_k^{1/2}, ω = 9β/γ^{1/2}, for the start (ζe, 0, ζe)
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$, search directions $(\Delta x^k,\Delta\lambda^k,\Delta s^k)$, $\mu_k = (x^k)^{\mathsf T}s^k/n$ and $D^k = (X^k)^{1/2}(S^k)^{-1/2}$. Assume $n \ge 1$, that the start is $(x^0,\lambda^0,s^0) = (\zeta e, 0, \zeta e)$ with $\|(x^*,s^*)\|_\infty \le \zeta$ for some primal-dual solution $(x^*,\lambda^*,s^*)$, and that it is infeasible, $(r_b^0,r_c^0) \ne 0$. Then, with
--
--   $$\omega = \frac{9\beta}{\gamma^{1/2}},$$
--
--   a constant independent of $n$, every iterate satisfies
--
--   $$\|(D^k)^{-1}\Delta x^k\| \le \omega n\,\mu_k^{1/2}, \qquad \|D^k\Delta s^k\| \le \omega n\,\mu_k^{1/2}.$$
--
--   This is the version of Lemma 6.5 with the dependence on $n$ explicit, the ingredient for the polynomial lower bound on the step length.
--
--   **Formalization Note** The book states "there is a constant $\omega$ independent of $n$"; the proof (p. 118) sets $\omega = 9\beta/\gamma^{1/2}$, and the statement uses this explicit value, which depends only on $\beta$ and $\gamma$. The solution in (6.13) makes $\Omega$ nonempty; $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit. Euclidean norms are written out explicitly.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 117, Lemma 6.6 (proof p. 118, ω = 9β/γ^{1/2}); starting point (6.12)–(6.13), p. 112; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Lemma 6.6 (pp. 117–118): with the starting point (6.12)–(6.13), the bounds of Lemma 6.5 hold
with `C₂ = ωn`, where `ω = 9β/γ^{1/2}` (the constant the proof on p. 118 sets) does not depend
on `n`: `‖(Dᵏ)⁻¹Δxᵏ‖ ≤ ωnμ_k^{1/2}` and `‖DᵏΔsᵏ‖ ≤ ωnμ_k^{1/2}` for all `k`. -/
theorem lemma_6_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (ζ : ℝ) (hx0 : x 0 = fun _ => ζ) (hlam0 : lam 0 = 0) (hs0 : s 0 = fun _ => ζ)
    (hζ : ∃ p ∈ Omega A b c, ∀ i, |p.1 i| ≤ ζ ∧ |p.2.2 i| ≤ ζ) :
    ∀ k,
      norm2 (scaledDx (x k) (s k) (dx k)) ≤
        (9 * β / Real.sqrt γ) * n * Real.sqrt (mu (x k) (s k)) ∧
      norm2 (scaledDs (x k) (s k) (ds k)) ≤
        (9 * β / Real.sqrt γ) * n * Real.sqrt (mu (x k) (s k)) := by sorry

end WrightPDIPM.Infeasible
