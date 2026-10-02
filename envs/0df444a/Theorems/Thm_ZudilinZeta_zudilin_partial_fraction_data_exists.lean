-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_data_exists
-- name    : ZudilinZeta.zudilin_partial_fraction_data_exists
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T12:11:06.081332+00:00
-- url     : https://prove2.me/theorems/693feb5e-8e73-4dee-b74d-bca2af19eced
-- title:
--   Partial fractions, reflection symmetry, and residue cancellation for $R_n$
-- statement:
--   For every admissible parameter system $P$ and every integer $n>0$, the rational function $R_n$ admits a partial-fraction datum as defined in `ZudilinZetaPartialFractions`:
--   $$
--   \exists (c_{s,k})\in\mathbb Q^{\mathbb N\times\mathbb N},\quad
--   R_n(t)=\sum_{s=1}^{q-r}\sum_{k=h_{r+1}}^{h_0-h_{r+1}}\frac{c_{s,k}}{(t+k)^s}\qquad(t>-1).
--   $$
--   The datum additionally satisfies
--   $$
--   c_{s,h_0-k}=(-1)^{s+1}c_{s,k}\quad(1\le s\le q-r,\ h_{r+1}\le k\le h_0-h_{r+1}),
--   \qquad \sum_{k=h_{r+1}}^{h_0-h_{r+1}}c_{1,k}=0.
--   $$
--   This is the finite algebraic input for expressing the derivative series as a linear form in odd zeta values. The function $R_n$ and all parameter conditions are those of the 2001 note, including the factor $h_0+2t$.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, definition of R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 19 and its proof, pp. 31–33, equations (8.10)–(8.12).

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

theorem zudilin_partial_fraction_data_exists (P : Params) (n : ℕ) (hn : 0 < n) :
    Nonempty (PartialFractionData P n) := by sorry

end ZudilinZeta
