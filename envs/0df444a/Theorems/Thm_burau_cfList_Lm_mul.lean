-- Prove2me | Theorems.Thm_burau_cfList_Lm_mul
-- name    : burau_cfList_Lm_mul
-- status  : Open
-- author  : @lt9
-- created : 2026-09-30T17:33:40.315001+00:00
-- url     : https://prove2.me/theorems/cecf23cd-2040-40a8-8fc0-8aaf877837cf
-- title:
--   Row-operation invariance of the continued fraction descent
-- statement:
--   **Row-operation invariance of the continued fraction descent.**
--
--   The quotient list $\mathtt{cfList}(M)$ of the Euclidean descent
--   $M\mapsto (M\,T^{-n})\,S$, $n=M_{01}/M_{00}$, depends only on the *first row* of $M$. Indeed left
--   multiplication by the lower triangular matrix
--   $$L^{-d}=\begin{pmatrix}1&0\\-d&1\end{pmatrix}$$
--   acts only on the second row, while the descent's quotient reads the first row and its successor map
--   $M\mapsto(M\,T^{-n})S$ is linear in the rows. Hence for every integral $2\times2$ matrix $M$ and every
--   $d$,
--   $$ \mathtt{cfList}\bigl(L^{-d}\,M\bigr)=\mathtt{cfList}(M),\qquad
--      \mathtt{cfEnd}\bigl(L^{-d}\,M\bigr)=L^{-d}\,\mathtt{cfEnd}(M). $$
--   Since $S\,T^{d}\,S^{-1}=L^{-d}$, this yields the shift law
--   $\mathtt{cfList}(S\,T^{d}\,L^{e})=\mathtt{cfList}(S\,L^{e})$: the quotient list of the terminal family
--   does not depend on $d$. This is a general structural theorem about the descent (it isolates the exact
--   dependence on the first row) and is used in the continued fraction reversal step of the
--   $S$-rule $\rho(M\cdot S)=\rho(M)\,\mathrm{lift}(S)$.
-- source:
--   Euclidean algorithm / continued fraction normal form for SL(2,Z); cf. J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Mathlib

open Matrix

namespace BurauNC

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `S = !![0,-1;1,0]` (matrix form). -/
def Sm : M2 := !![0, -1; 1, 0]

/-- `T^n = !![1,n;0,1]` (matrix form). -/
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

/-- **Budget invariance**: once the budget reaches the descent measure `(M 0 0).natAbs`, extra steps
change nothing (the recursion stops at the terminal case). -/

noncomputable def cfList : M2 → List ℤ
  | M => if h : M 0 0 = 0 then []
    else (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm)
termination_by M => (M 0 0).natAbs
decreasing_by exact euclid_decrease M h

theorem cfList_cons (M : M2) (h : M 0 0 ≠ 0) :
    cfList M = (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm) := by
  rw [cfList.eq_def]
  exact dif_neg h

/-- The `Q`-word recorded by the descent with quotient list `l` (the outer factor `S⁻¹T^e` is applied
last, matching `rhoIter`'s right-appending order). -/

theorem cfList_eq_nil (M : M2) (h : M 0 0 = 0) : cfList M = [] := by
  rw [cfList.eq_def]
  exact dif_pos h

/-- **The descent in terms of the quotient list**: `ρ` is the terminal `baseQ` value followed by the
recorded factors. -/

noncomputable def Lm (k : ℤ) : M2 := !![1, 0; k, 1]


theorem Lm_mul_zero_zero (d : ℤ) (M : M2) : (Lm (-d) * M) 0 0 = M 0 0 := by
  simp [Lm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Lm_mul_zero_one (d : ℤ) (M : M2) : (Lm (-d) * M) 0 1 = M 0 1 := by
  simp [Lm, Matrix.mul_apply, Fin.sum_univ_two]


end BurauNC

theorem burau_cfList_Lm_mul (d : ℤ) (M : BurauNC.M2) :
    BurauNC.cfList (BurauNC.Lm (-d) * M) = BurauNC.cfList M := by sorry
