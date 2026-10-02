-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_pole_support
-- name    : ZudilinZeta.zudilin_partial_fraction_pole_support
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T13:51:18.498854+00:00
-- url     : https://prove2.me/theorems/a951fd0c-6cc4-4e06-b943-32d8b7729fda
-- title:
--   Sharp support for partial-fraction coefficients of each order
-- statement:
--   For admissible parameters $P$, $n>0$, and any partial-fraction datum $(c_{s,k})$ for the mission rational function $R_n$, put $S=q-r$ and $K=\{h_{r+1},\ldots,h_0-h_{r+1}\}$. Then
--   $$
--    c_{s,k}=0\quad\text{if }1\le s\le S,\ k\in K,\ \text{and }k\notin\{h_{r+s},\ldots,h_0-h_{r+s}\}.
--   $$
--   The denominator intervals are nested. Outside the displayed interval fewer than $s$ denominator factors have a pole at $-k$, so the order-$s$ coefficient vanishes. The assertion concerns every datum satisfying the expansion on $t>-1$; uniqueness of rational partial fractions transfers the pole-order calculation to any such datum.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially (8.10)–(8.12).

import Definitions.Def_ZudilinZetaCoefficientArithmetic

namespace ZudilinZeta

theorem zudilin_partial_fraction_pole_support (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    ∀ s ∈ Finset.Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n,
      k ∉ orderPoleRange P n s → d.coeff s k = 0 := by sorry

end ZudilinZeta
