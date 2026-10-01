-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq
-- name    : ZudilinZeta.zudilin_phi_tail_integral_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T09:52:24.92373+00:00
-- url     : https://prove2.me/theorems/199d67f8-acda-47dd-b413-9e5ee4bc2717
-- title:
--   Periodic tail integral in the constant $C_1$
-- statement:
--   Let $P$ be an admissible parameter tuple of Zudilin's note. Let $\varphi$ be its integer-valued periodic function, let $m=m_{q-r}$, and let $\psi=(\log\Gamma)'$. Then
--
--   $$
--   \int_{1/m}^{\infty}\frac{\varphi(x)}{x^2}\,dx
--   =
--   \int_0^1\varphi(x)\psi'(x)\,dx
--   -
--   \int_0^{1/m}\frac{\varphi(x)}{x^2}\,dx.
--   $$
--
--   This identity connects the tail-integral formulation of the prime-product growth rate with the subtracted term in the definition of $C_1$ in Lemma 3. It is an auxiliary identity implicit in that definition, rather than a separately numbered lemma of the note.
--
--   **Formalization Note** The tail integral uses Lebesgue measure on $(1/m,\infty)$; the two bounded integrals are interval integrals. All functions are the mission's existing definitions.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56:4 (2001), 774–776, p. 775; https://doi.org/10.1070/RM2001v056n04ABEH000427; full text https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&option_lang=eng&paperid=427&what=fullteng. Arithmetic discussion after Lemma 1 and the definition of C1 in Lemma 3.

import Definitions.Def_ZudilinZetaAsymp

namespace ZudilinZeta

theorem zudilin_phi_tail_integral_eq (P : Params) :
    (∫ x in Set.Ioi (1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2) =
      (∫ x in (0 : ℝ)..1, (phi P x : ℝ) * deriv digamma x) -
        ∫ x in (0 : ℝ)..(1 / (m P (P.q - P.r) : ℝ)),
          (phi P x : ℝ) / x ^ 2 := by sorry

end ZudilinZeta
