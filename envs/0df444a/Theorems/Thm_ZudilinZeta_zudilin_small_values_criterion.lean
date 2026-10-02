-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_small_values_criterion
-- name    : ZudilinZeta.zudilin_small_values_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:37:08.889631+00:00
-- url     : https://prove2.me/theorems/45d09a3f-caed-4907-af7a-8f25a6ede4ac
-- title:
--   Small nonzero values of the forms (3) force an irrational among (4)
-- statement:
--   The note states, between Lemmas 2 and 3: *if the sequence of linear forms on the left-hand side of (3) takes nonzero arbitrarily small values as $n$ grows, then in the case $r = 3$ there is an irrational number among*
--   $$\zeta(5),\ \zeta(7),\ \dots,\ \zeta(q-4),\ \zeta(q-2). \tag{4}$$
--
--   Formally: assume $r = 3$ and that for every $\varepsilon > 0$ there is an $n > 0$ with $\Lambda_n \ne 0$ and $|\Lambda_n| < \varepsilon$, where $\Lambda_n = D^r_{m_1 n}D_{m_2 n}\cdots D_{m_{q-r}n}\Phi_n^{-1}F_n$ is the left-hand side of (3). Then at least one of $\zeta(r+2k)$, $k = 1, \dots, (q-r-2)/2$, is irrational.
--
--   This is the classical linear-form criterion applied to (3): by Lemma 1 the numbers $\Lambda_n$ lie in $\mathbb{Z} + \mathbb{Z}\zeta(5) + \dots + \mathbb{Z}\zeta(q-2)$, and a nonzero integral linear combination of rationals cannot be arbitrarily small.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaArith

namespace ZudilinZeta
theorem zudilin_small_values_criterion (P : Params) (hr : P.r = 3)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ Lambda P n ≠ 0 ∧ |Lambda P n| < ε) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by sorry
end ZudilinZeta
