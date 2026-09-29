-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_lemma2
-- name    : ZudilinZeta.zudilin_lemma2
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-22T18:32:45.985202+00:00
-- url     : https://prove2.me/theorems/f96f8571-c629-4d22-93b7-56edae45a669
-- title:
--   Lemma 2: $\overline{\lim}\,\log|F_n|/n = \operatorname{Re} f_0(\tau_0)$
-- statement:
--   **Lemma 2 of the note.** Let $r = 3$ and let $\tau_0$ be a zero of the polynomial
--   $$(\tau-\eta_0)^r(\tau-\eta_1)\cdots(\tau-\eta_q) - \tau^r(\tau-\eta_0+\eta_1)\cdots(\tau-\eta_0+\eta_q)$$
--   with $\operatorname{Im}\tau_0 > 0$ and with the largest possible value of $\operatorname{Re}\tau_0$. Assume $\operatorname{Re}\tau_0 < \eta_0$ and $\operatorname{Im} f_0(\tau_0) \notin \pi\mathbb{Z}$. Then
--   $$\varlimsup_{n \to \infty} \frac{\log|F_n|}{n} = \operatorname{Re} f_0(\tau_0).$$
--
--   The note proves this by writing (2) as a complex integral along a vertical line $\operatorname{Re} t = \mathrm{const}$ and applying the asymptotics of the gamma function together with the saddle-point method.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaAsymp

namespace ZudilinZeta
theorem zudilin_lemma2 (P : Params) (hr : P.r = 3) (τ₀ : ℂ)
    (hroot : charPoly P τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly P τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re)
    (hre : τ₀.re < (P.eta 0 : ℝ)) (hpi : ∀ k : ℤ, (f0 P τ₀).im ≠ (k : ℝ) * Real.pi) :
    Filter.limsup (fun n : ℕ => Real.log |F P n| / (n : ℝ)) Filter.atTop = (f0 P τ₀).re := by
  sorry
end ZudilinZeta
