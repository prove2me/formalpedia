-- Prove2me | Theorems.Thm_burau_cfList_eq_cfPair
-- name    : burau_cfList_eq_cfPair
-- status  : Open
-- author  : @lt9
-- created : 2026-09-30T19:39:09.746859+00:00
-- url     : https://prove2.me/theorems/e2d39785-ecfe-4bf1-9abe-07f403026cab
-- title:
--   The Burau descent depends only on the first row
-- statement:
--   **The Euclidean descent of the Burau section depends only on the first row.**
--
--   The section $\rho$ of the specialization $Q\to\mathrm{SL}(2,\mathbb Z)$ is built from the subtractive
--   Euclidean descent $M\mapsto (M\,T^{-n})\,S$ with $n=M_{01}/M_{00}$. Its recorded quotient list is
--   $\mathtt{cfList}\,M$, defined by
--   $$\mathtt{cfList}\,M=\begin{cases}[] & M_{00}=0,\\ \frac{M_{01}}{M_{00}}::\mathtt{cfList}\bigl((M\,T^{-M_{01}/M_{00}})\,S\bigr)&\text{else,}\end{cases}$$
--   so the quotient is read off the first row and the successor map acts linearly on the rows. Consequently
--   the whole quotient list is computed by the pure integer recursion
--   $$\mathtt{cfPair}(a,b)=\begin{cases}[] & a=0\\ \frac ba::\mathtt{cfPair}\bigl(b\bmod a,\,-a\bigr)&\text{else}\end{cases}$$
--   and for every integral matrix $M$
--   $$\mathtt{cfList}\,M=\mathtt{cfPair}\,M_{00}\,M_{01}.$$
--   This separates the arithmetic of the descent (the Euclidean algorithm) from the matrix bookkeeping, and
--   is the form in which the remaining continued-fraction reversal step of the $S$-rule is stated.
-- source:
--   Euclidean algorithm / continued fractions for SL(2,Z); see Birman, Ann. of Math. Studies 82 (1974), §3.3.

import Mathlib

open Matrix

namespace BurauNC

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ


def Sm : M2 := !![0, -1; 1, 0]


def Tm (n : ℤ) : M2 := !![1, n; 0, 1]

theorem euclid_decrease (M : M2) (h : M 0 0 ≠ 0) :
    (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs < (M 0 0).natAbs := by
  have hkey : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0) = M 0 1 % M 0 0 := by
    rw [Tm, Sm]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def]
    ring
  rw [hkey, Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr ((abs_of_nonneg (Int.emod_nonneg (M 0 1) h)).trans_lt
    (Int.emod_lt_abs (M 0 1) h))

noncomputable def cfList : M2 → List ℤ
  | M => if h : M 0 0 = 0 then []
    else (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm)
termination_by M => (M 0 0).natAbs
decreasing_by exact euclid_decrease M h

theorem cfList_cons (M : M2) (h : M 0 0 ≠ 0) :
    cfList M = (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm) := by
  rw [cfList.eq_def]
  exact dif_neg h

theorem cfList_eq_nil (M : M2) (h : M 0 0 = 0) : cfList M = [] := by
  rw [cfList.eq_def]
  exact dif_pos h

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


theorem ediv_neg_divisor (a b : ℤ) : b / (-a) = -(b / a) := Int.ediv_neg b a


theorem emod_neg_divisor (a b : ℤ) : b % (-a) = b % a := Int.emod_neg b a

end BurauNC

theorem burau_cfList_eq_cfPair (M : BurauNC.M2) :
    BurauNC.cfList M = BurauNC.cfPair (M 0 0) (M 0 1) := by sorry
