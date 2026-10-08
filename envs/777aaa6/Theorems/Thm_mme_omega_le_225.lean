-- Prove2me | Theorems.Thm_mme_omega_le_225
-- name    : mme_omega_le_225
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T04:46:41.35242+00:00
-- url     : https://prove2.me/theorems/f2b5622a-3bca-4b8f-92a1-381d10af16e3
-- title:
--   Matrix multiplication exponent ≤ 2.25 over every field
-- statement:
--   For every universe level $u$ and every field $K$ whose underlying type belongs to that universe, with no restriction on its characteristic or cardinality and no additional hypotheses beyond the nontrivial commutative field axioms, the real number $\operatorname{matMulExp}(K)$ defined below satisfies the non-strict inequality $\operatorname{matMulExp}(K)\leq 2.25=9/4$. For each natural number $n$, including $n=0$, let $I_n=\{0,\ldots,n-1\}$, with $I_0=\varnothing$, and let $V_n$ be the $K$-vector space of all functions $I_n\times I_n\to K$, with pointwise operations. For $i,j\in I_n$, let $e_{ij}\in V_n$ have value $1$ at $(i,j)$ and $0$ elsewhere, and define $T_n=\sum_{i,j,k\in I_n}e_{ij}\otimes_K e_{jk}\otimes_K e_{ki}$ in the tensor product of three copies of $V_n$. The natural number $R_K(T_n)$ used here is the infimum in $\mathbb N$ of all natural numbers $r$ for which there exist vectors $a_q,b_q,c_q\in V_n$, indexed by $q=0,\ldots,r-1$, such that $T_n=\sum_{q=0}^{r-1}a_q\otimes_K b_q\otimes_K c_q$; the vectors need not be nonzero. Thus it is the least such $r$ when a decomposition exists, and the natural-number infimum convention gives $0$ if the set of decomposition lengths is empty; that empty-set case does not occur for $T_n$, since its displayed finite sum is a decomposition. The empty sum is allowed when $r=0$, so the zero tensor has rank $0$ and $T_0=0$. Explicitly, $\operatorname{matMulExp}(K)=\inf_{n\in\mathbb N}a_n$, where $a_0=a_1=3$ and $a_n=\log(R_K(T_n))/\log n$ for every $n\geq2$, with the natural numbers in this quotient regarded as real numbers. The real logarithm and division are total functions, with $\log 0=0$ and $x/0=0$; the denominator in the quotient actually used is positive, and a rank of $0$ or $1$ would give quotient $0$. The infimum is the real infimum operation, which returns $0$ for an empty set or a set unbounded below; here its set of values is nonempty and bounded below by $0$, so it is the ordinary greatest lower bound. The asserted upper bound is on this infimum and does not assert that it is attained at any particular matrix size.

import Definitions.Def_mme_omega
universe u
open MME

theorem mme_omega_le_225 {K : Type u} [Field K] :
    matMulExp K ≤ (2.25 : ℝ) := by
  sorry
