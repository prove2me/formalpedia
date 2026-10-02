-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_partial_fraction_prime_bound
-- name    : ZudilinZeta.zudilin_partial_fraction_prime_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T14:34:30.526756+00:00
-- url     : https://prove2.me/theorems/6dfafe71-55b8-4755-b5ac-86a18533cb89
-- title:
--   Selected-prime valuation bound for Zudilin’s coefficients
-- statement:
--   Let $P$ be admissible, let $n>0$, and let $(c_{s,k})$ be any partial-fraction datum for the mission rational function $R_n$, including $h_0+2t$. Write $S=q-r$. For $1\le s\le S$, $h_{r+1}\le k\le h_0-h_{r+1}$, and $c_{s,k}\ne0$, every prime satisfying
--   $$
--   \eta_0n<p^2,\qquad p\le m_Sn
--   $$
--   obeys
--   $$
--   v_p(c_{s,k})\ge -(S-s)+\phi(n/p).
--   $$
--   Here $v_p$ is the integer-valued valuation on nonzero rational numbers, and $\phi$ is the periodic minimum of floor expressions from the mission. The nonzero hypothesis is explicit because Lean’s total valuation function assigns a finite default to zero. This is the prime improvement for the individual coefficients used in the mission’s product $\Phi_n$; the square cutoff is the exact one from the 2001 note.
-- source:
--   W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially inequalities (8.10)–(8.11); One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, Lemma 1 and the exact prime cutoff, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf.

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

theorem zudilin_partial_fraction_prime_bound (P : Params) (n : ℕ) (hn : 0 < n)
    (d : PartialFractionData P n) :
    ∀ s ∈ Finset.Icc 1 (P.q-P.r), ∀ k ∈ poleRange P n, d.coeff s k ≠ 0 →
      ∀ p : ℕ, p.Prime → P.eta 0*n < p*p → p ≤ m P (P.q-P.r)*n →
        -((P.q-P.r-s : ℕ) : ℤ) + phi P ((n : ℝ)/(p : ℝ)) ≤
          padicValRat p (d.coeff s k) := by sorry

end ZudilinZeta
