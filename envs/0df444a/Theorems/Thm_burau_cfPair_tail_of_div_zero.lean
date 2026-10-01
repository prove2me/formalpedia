-- Prove2me | Theorems.Thm_burau_cfPair_tail_of_div_zero
-- name    : burau_cfPair_tail_of_div_zero
-- status  : Open
-- author  : @lt9
-- created : 2026-09-30T17:26:06.350542+00:00
-- url     : https://prove2.me/theorems/ae1f4e6a-543a-4637-8ebe-c73d133eea1d
-- title:
--   Continued fraction reversal: the vanishing-quotient base case
-- statement:
--   **Base case of the continued fraction reversal, at the integer level.**
--
--   The section $\rho$ of $\mathrm{SL}(2,\mathbb Z)$ is built from the subtractive Euclidean descent
--   $M\mapsto (M\cdot T^{-n})\cdot S$ with $n=M_{01}/M_{00}$, whose recorded quotient list is computed by
--   $$ \mathtt{cfPair}(a,b)=\begin{cases}[] & a=0\\ \frac{b}{a}::\mathtt{cfPair}(b\bmod a,\,-a)&\text{else,}\end{cases}$$
--   a recursion on integers alone (proved elsewhere to agree with the matrix descent:
--   $\mathtt{cfList}\,M=\mathtt{cfPair}\,M_{00}\,M_{01}$). Then, whenever the leading quotient vanishes,
--   the $(b,-a)$ descent is the tail of the $(a,b)$ descent:
--   $$ \frac ba = 0\ \Longrightarrow\ \mathtt{cfPair}(b,-a)=\operatorname{tail}\bigl(\mathtt{cfPair}(a,b)\bigr). $$
--   Equivalently: if $|b|<|a|$ then the continued fraction of $-1/(b/a)$ is obtained from that of $b/a$ by
--   prepending a zero — the first (and only elementary) case of continued fraction reciprocity, matching the
--   already proved base case of the $S$-rule $\rho(M\cdot S)=\rho(M)\,\mathrm{lift}(S)$ at the matrix level.
-- source:
--   Continued fraction reversal / continuant symmetry; cf. J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3; C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964).

import Mathlib

namespace BurauNC

/-- The descent restricted to the first row: the quotient list of the Euclidean algorithm on `b/a`. -/
noncomputable def cfPair (a b : ℤ) : List ℤ :=
  if h : a = 0 then [] else b / a :: cfPair (b % a) (-a)
termination_by a.natAbs
decreasing_by
  have h1 : 0 ≤ b % a := Int.emod_nonneg b h
  have h2 : b % a < |a| := Int.emod_lt_abs b h
  have h3 : |b % a| < |a| := by rwa [abs_of_nonneg h1]
  rw [Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr h3

theorem cfPair_cons (a b : ℤ) (h : a ≠ 0) : cfPair a b = b / a :: cfPair (b % a) (-a) := by
  rw [cfPair.eq_def]
  exact dif_neg h

theorem cfPair_zero (b : ℤ) : cfPair 0 b = [] := by
  rw [cfPair.eq_def]
  exact dif_pos rfl

/-- Negating the *divisor* negates the Euclidean quotient … -/
theorem ediv_neg_divisor (a b : ℤ) : b / (-a) = -(b / a) := Int.ediv_neg b a

/-- … while the Euclidean remainder is unchanged. This is the structural basis of the continued
fraction reversal: the two descents `(a,b) ↦ (b % a, -a)` and `(b,-a) ↦ (b % a, -b)` share the same
remainders with opposite quotient signs. -/
theorem emod_neg_divisor (a b : ℤ) : b % (-a) = b % a := Int.emod_neg b a

end BurauNC

theorem burau_cfPair_tail_of_div_zero (a b : ℤ) (ha : a ≠ 0) (h : b / a = 0) :
    BurauNC.cfPair b (-a) = (BurauNC.cfPair a b).tail := by sorry
