-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_saddle_log_side_conditions
-- name    : ZudilinZeta.zudilin_saddle_log_side_conditions
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T09:52:28.635602+00:00
-- url     : https://prove2.me/theorems/ebdb1d9c-74aa-4913-be8e-12e93f2848f4
-- title:
--   Bounded logarithmic rates and nonvanishing for the saddle-point forms
-- statement:
--   Let $P$ be admissible with $r=3$, and let $\tau_0$ satisfy the saddle-point hypotheses of Lemma 2: it is a zero of the characteristic polynomial, has positive imaginary part and maximal real part among such zeros, satisfies $\operatorname{Re}\tau_0<\eta_0$, and obeys $\operatorname{Im}f_0(\tau_0)\notin\pi\mathbb Z$.
--
--   For the linear forms $F_n$ in (2), the logarithmic rates are eventually bounded above, and nonzero forms occur at arbitrarily large indices:
--
--   $$
--   \left(\exists B\in\mathbb R\;\exists N\in\mathbb N\;\forall n\ge N:\quad
--   \frac{\log|F_n|}{n}\le B\right)
--   \quad\text{and}\quad
--   \left(\forall N\in\mathbb N\;\exists n\ge N:\quad F_n\ne0\right).
--   $$
--
--   These are analytic side conditions of the finite exponential-rate assertion obtained by the saddle-point method in Lemma 2. They permit the existing real-valued limsup statement to be used to produce arbitrarily small nonzero normalized forms.
--
--   **Formalization Note** Lean's real logarithm satisfies $\log 0=0$, and its real-valued limsup alone does not certify boundedness or nonvanishing. The displayed logarithmic rate uses these totalized real operations, including division at $n=0$; the eventual statements ignore that initial index. Boundedness and nonvanishing are separate proof obligations here, not consequences asserted solely from the existing formal limsup equality.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56:4 (2001), 774–776, p. 775; https://doi.org/10.1070/RM2001v056n04ABEH000427; full text https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&option_lang=eng&paperid=427&what=fullteng. Lemma 2 and the immediately following passage from (3) to (4); explicit side conditions of the saddle-point asymptotic.

import Definitions.Def_ZudilinZetaAsymp

namespace ZudilinZeta

theorem zudilin_saddle_log_side_conditions (P : Params) (hr : P.r = 3) (τ₀ : ℂ)
    (hroot : charPoly P τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly P τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re)
    (hre : τ₀.re < (P.eta 0 : ℝ))
    (hpi : ∀ k : ℤ, (f0 P τ₀).im ≠ (k : ℝ) * Real.pi) :
    Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) Filter.atTop
        (fun n : ℕ => Real.log |F P n| / (n : ℝ)) ∧
      (∃ᶠ n : ℕ in Filter.atTop, F P n ≠ 0) := by sorry

end ZudilinZeta
