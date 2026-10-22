-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_lemma_6_7_special
-- name    : WrightPDIPM.Infeasible.lemma_6_7_special
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:59.99582+00:00
-- url     : https://prove2.me/theorems/bc118a80-d046-4d21-ad47-050a6561dc41
-- title:
--   Lemma 6.7, second part (6.38) — ᾱ ≥ δ̄/n² for the start (ζe, 0, ζe), δ̄ independent of n
-- statement:
--   Fix parameters $\gamma \in (0,1)$, $\beta \ge 1$ and $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$ of Algorithm IPF. Then there is a positive scalar $\bar\delta$, depending on these parameters only, with the following property. For every linear program with data $A \in \mathbb{R}^{m\times n}$ ($n \ge 1$), $b$, $c$, and every run of Algorithm IPF from the starting point $(x^0,\lambda^0,s^0) = (\zeta e, 0, \zeta e)$, where $\|(x^*,s^*)\|_\infty \le \zeta$ for some primal-dual solution $(x^*,\lambda^*,s^*)$ and $(r_b^0,r_c^0) \ne 0$, there is $\bar\alpha \in (0,1)$ with
--
--   $$\bar\alpha \ge \bar\delta/n^2$$
--
--   such that for all $\alpha \in [0,\bar\alpha]$ and all $k \ge 0$ the inequalities (6.37a)–(6.37c) of Lemma 6.7 hold, and hence the step-length conditions (6.5) and (6.6) hold.
--
--   The step lengths of the method are therefore bounded below by an inverse polynomial in $n$, which yields the $O(n^2|\log\epsilon|)$ iteration bound of Theorem 6.2.
--
--   **Formalization Note** "$\bar\delta$ independent of $n$" is rendered by quantifying $\bar\delta$ after the parameters $\gamma, \beta, \sigma_{\min}, \sigma_{\max}$ and before the dimension, the data and the run. The book leaves the proof of this part as Exercise 4 (p. 125); it does not give $\bar\delta$ explicitly, and the statement keeps it existential. The conclusion repeats the five conditions of the first part so that the $\bar\alpha$ bounded here is the same kind of object as in Lemma 6.7. $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit; the solution in (6.13) makes $\Omega$ nonempty, and the special start lies in $\mathcal N_{-\infty}(\gamma,\beta)$ automatically.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 118, Lemma 6.7, second part, Eq. (6.38) (proof left as Exercise 4, p. 125); starting point (6.12)–(6.13), p. 112; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Lemma 6.7, second part (6.38) (p. 118): there is `δ̄ > 0`, depending only on the parameters
`γ, β, σ_min, σ_max` and not on `n` or on the instance, such that for every run of Algorithm IPF
from the starting point (6.12)–(6.13) of Lemma 6.6 the conclusion of the first part holds with
some `ᾱ ∈ (0, 1)` satisfying `ᾱ ≥ δ̄/n²`. -/
theorem lemma_6_7_special (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5) :
    ∃ δbar : ℝ, 0 < δbar ∧
    ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (ζ : ℝ) (hx0 : x 0 = fun _ => ζ) (hlam0 : lam 0 = 0) (hs0 : s 0 = fun _ => ζ)
    (hζ : ∃ p ∈ Omega A b c, ∀ i, |p.1 i| ≤ ζ ∧ |p.2.2 i| ≤ ζ),
    ∃ αbar : ℝ, 0 < αbar ∧ αbar < 1 ∧ δbar / (n : ℝ) ^ 2 ≤ αbar ∧
      ∀ a ∈ Set.Icc (0 : ℝ) αbar, ∀ k,
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≥ (1 - a) * (x k ⬝ᵥ s k) ∧
        (∀ i, (x k i + a * dx k i) * (s k i + a * ds k i) ≥
          (γ / n) * ((x k + a • dx k) ⬝ᵥ (s k + a • ds k))) ∧
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≤ (1 - 0.01 * a) * (x k ⬝ᵥ s k) ∧
        (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈
          NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
        mu (x k + a • dx k) (s k + a • ds k) ≤ (1 - 0.01 * a) * mu (x k) (s k) := by sorry

end WrightPDIPM.Infeasible
