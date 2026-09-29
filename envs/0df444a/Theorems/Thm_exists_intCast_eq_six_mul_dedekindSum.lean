-- Prove2me | Theorems.Thm_exists_intCast_eq_six_mul_dedekindSum
-- name    : exists_intCast_eq_six_mul_dedekindSum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a3774e60-37f6-5d7b-9723-3882ff075f07
-- title:
--   Integrality of 6k s(h,k) for Dedekind sums
-- statement:
--   Let $h$ and $k$ be natural numbers with $k > 0$. Here the Dedekind sum is the rational number $$s(h,k)=\sum_{r=0}^{k-1}\left(\!\left(\frac{r}{k}\right)\!\right)\left(\!\left(\frac{hr}{k}\right)\!\right),$$ where the sawtooth function [`dedekindSaw`](def/NumberTheory_DedekindSum.html#L11) is defined on $\mathbb{Q}$ by $((x)) = \operatorname{frac}(x) - 1/2$ when the fractional part $\operatorname{frac}(x)$ is nonzero, and $((x)) = 0$ when $\operatorname{frac}(x) = 0$; the index $h$ is taken as an integer through the inclusion $\mathbb{N} \hookrightarrow \mathbb{Z}$, and the summation runs over $r \in \{0, 1, \dots, k-1\}$. The assertion is that there exists an integer $z$ whose image in $\mathbb{Q}$ equals $6k\,s(h,k)$, that is, $6k\,s(h,k)$ lies in the image of $\mathbb{Z}$ in $\mathbb{Q}$. No coprimality between $h$ and $k$ is assumed; the statement is purely the integrality of the denominator-cleared sum, and no explicit formula for $z$ is provided by the conclusion.
--
--   This is the classical integrality property of Dedekind sums: the denominator of $s(h,k)$ divides $6k$. It is used in the congruence [`dedekindSum_jacobiSym_mod_eight`](thm.html#dedekindSum_jacobiSym_mod_eight), which compares $s(h,k)$ with a Jacobi symbol modulo $8$ and so requires the integrality of $6k\,s(h,k)$ as a preliminary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_intCast_eq_six_mul_dedekindSum.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem exists_intCast_eq_six_mul_dedekindSum (h k : ℕ) (hk : 0 < k) : ∃ z : ℤ, (z : ℚ) = 6 * k * dedekindSum h k := by sorry
