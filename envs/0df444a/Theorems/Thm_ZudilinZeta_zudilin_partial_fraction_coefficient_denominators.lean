-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_coefficient_denominators
-- name    : ZudilinZeta.zudilin_partial_fraction_coefficient_denominators
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T13:51:27.880527+00:00
-- url     : https://prove2.me/theorems/0299dbf5-7478-4343-84af-c8da39187e5b
-- title:
--   Prime-improved denominator bound for each partial-fraction coefficient
-- statement:
--   Let $P$ be admissible, let $n>0$, and let $(c_{s,k})$ be any partial-fraction datum for the mission rational function $R_n$, including its factor $h_0+2t$. For every $1\le s\le S=q-r$ and every $k$ in the full pole interval,
--   $$
--   \frac{\prod_{j=s+1}^{S}D_{m_jn}}{\Phi_n}\,c_{s,k}\in\mathbb Z.
--   $$
--   The product is empty, hence $1$, for $s=S$. This is an individual coefficient estimate; it contains no zeta sum or harmonic constant. It packages the elementary-brick arithmetic used in Lemma 19: the rough bound $D_{m_0n}^{S-s}c_{s,k}\in\mathbb Z$, with $m_0=\max(\eta_r,\eta_0-2\eta_{r+1})$, together with the prime valuation improvement by $\phi(n/p)$. Since $m_j\ge m_0$, the tail lcm product clears the rough denominators; each prime selected in $\Phi_n$ occurs once in each tail lcm because $p\le m_Sn\le m_jn\le\eta_0n<p^2$. The prime cutoff here is exactly that of the mission's 2001 note. The normalized local coefficients must be computed after symbolic cancellation of the pole factors.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially (8.10)–(8.12).

import Definitions.Def_ZudilinZetaCoefficientArithmetic

namespace ZudilinZeta

theorem zudilin_partial_fraction_coefficient_denominators (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    ∀ s ∈ Finset.Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n,
      ∃ a : ℤ, tailDenominatorScale P n s * d.coeff s k = (a : ℚ) := by sorry

end ZudilinZeta
