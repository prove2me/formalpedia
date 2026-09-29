-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_phi_nonneg_periodic
-- name    : ZudilinZeta.zudilin_phi_nonneg_periodic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:17:24.877127+00:00
-- url     : https://prove2.me/theorems/50e8aa3f-e0f8-4763-a5d7-fd9ecca1887b
-- title:
--   $\varphi$ is nonnegative and $1$-periodic
-- statement:
--   The note states, right after defining $\varphi$, that it is an *integer-valued, nonnegative, periodic function with period $1$*. Integrality holds by construction (the defining expression is a sum of floors); the two remaining assertions are: $\varphi(x) \ge 0$ for every real $x$, and $\varphi(x+1) = \varphi(x)$ for every real $x$.
--
--   Nonnegativity is what makes $\Phi_n$ an integer dividing the relevant products, so it is used in Lemma 1; periodicity is what makes the integrals in the constant $C_1$ finite computations over $[0,1]$.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_phi_nonneg_periodic (P : Params) :
    (∀ x : ℝ, 0 ≤ phi P x) ∧ (∀ x : ℝ, phi P (x + 1) = phi P x) := by sorry
end ZudilinZeta
