-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_rough_denominators
-- name    : ZudilinZeta.zudilin_partial_fraction_rough_denominators
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T14:34:11.254207+00:00
-- url     : https://prove2.me/theorems/17f2471b-42dd-46a3-9204-af5879dc6829
-- title:
--   Rough lcm bound for Zudilin’s partial-fraction coefficients
-- statement:
--   Let $P$ be an admissible parameter system, let $n>0$, and let $(c_{s,k})$ be any partial-fraction datum for the mission rational function $R_n$. Put $S=q-r$ and
--   $$
--   m_0=\max\{\eta_r,\eta_0-2\eta_{r+1}\}.
--   $$
--   For every $1\le s\le S$ and every pole index $h_{r+1}\le k\le h_0-h_{r+1}$,
--   $$
--   D_{m_0n}^{S-s}\,c_{s,k}\in\mathbb Z.
--   $$
--   Here $D_N=\operatorname{lcm}(1,\ldots,N)$, and $D_0=1$. This is the rough coefficient denominator estimate in (8.10), before the improvement by the selected prime product. The rational function and its factor $h_0+2t$ are exactly those in the mission’s 2001 note.
-- source:
--   W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially inequalities (8.10)–(8.11); One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, Lemma 1 and the exact prime cutoff, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf.

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

theorem zudilin_partial_fraction_rough_denominators (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    ∀ s ∈ Finset.Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n,
      ∃ a : ℤ,
        (D (max (P.eta P.r) (P.eta 0-2*P.eta (P.r+1))*n) : ℚ)^(P.q-P.r-s) *
          d.coeff s k = (a : ℚ) := by sorry

end ZudilinZeta
