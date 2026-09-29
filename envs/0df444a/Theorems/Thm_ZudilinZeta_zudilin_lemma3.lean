-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_lemma3
-- name    : ZudilinZeta.zudilin_lemma3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-22T18:42:55.76398+00:00
-- url     : https://prove2.me/theorems/45eb7c10-d609-48a7-a18d-e93fbc244e87
-- title:
--   Lemma 3: $C_0 > C_1$ implies an irrational among (4)
-- statement:
--   **Lemma 3 of the note.** Let $r = 3$ and, in the notation above, let
--   $$C_0 = -\operatorname{Re} f_0(\tau_0), \qquad C_1 = rm_1 + m_2 + \dots + m_{q-r} - \Big(\int_0^1\varphi(x)\,\mathrm{d}\psi(x) - \int_0^{1/m_{q-r}}\varphi(x)\,\frac{\mathrm{d}x}{x^2}\Big),$$
--   where $\psi$ is the logarithmic derivative of the gamma function. Then in the case $C_0 > C_1$ at least one of the numbers (4), i.e. of $\zeta(5), \zeta(7), \dots, \zeta(q-2)$, is irrational.
--
--   $C_0$ is the decay rate of $|F_n|$ supplied by Lemma 2, and $C_1$ is the growth rate of the denominator $D^r_{m_1n}\cdots D_{m_{q-r}n}\Phi_n^{-1}$ supplied by the prime number theorem and the Chudnovsky–Rukhadze–Hata analysis of $\Phi_n$; $C_0 > C_1$ is exactly the statement that the forms $\Lambda_n$ are arbitrarily small.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaAsymp

namespace ZudilinZeta
theorem zudilin_lemma3 (P : Params) (hr : P.r = 3) (τ₀ : ℂ)
    (hroot : charPoly P τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly P τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re)
    (hre : τ₀.re < (P.eta 0 : ℝ)) (hpi : ∀ k : ℤ, (f0 P τ₀).im ≠ (k : ℝ) * Real.pi)
    (hC : C1 P < C0 P τ₀) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by sorry
end ZudilinZeta
