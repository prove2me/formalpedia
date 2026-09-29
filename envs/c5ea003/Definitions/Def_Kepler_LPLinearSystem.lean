-- Prove2me | Definitions.Def_Kepler_LPLinearSystem
-- name    : Kepler_LPLinearSystem
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T02:55:37.395985+00:00
-- url     : https://prove2.me/theorems/7a4bc634-124e-4ec6-9630-b46ad40fc466
-- title:
--   Exact rational LP systems and certificate checks
-- statement:
--   For arbitrary natural numbers $m,n$, including $0$, a rational linear system is a matrix $A\in\mathbb Q^{m\times n}$ together with bounds $b\in\mathbb Q^m$. A real vector $x\in\mathbb R^n$ is feasible exactly when $\sum_{j=0}^{n-1}A_{ij}x_j\leq b_i$ for every $0\leq i<m$, with rational coefficients interpreted in $\mathbb R$; there is no sign restriction on $x$. For any rational vector $y\in\mathbb Q^m$, the Boolean test returns true exactly when $y_i\geq0$ for every row, $\sum_{i=0}^{m-1}y_iA_{ij}=0$ for every column, and $\sum_{i=0}^{m-1}y_ib_i<0$. All three conditions are tested with exact rational arithmetic. If $m=0$, feasibility is vacuous and the test is false because its final sum is $0$. If $n=0$, there is one empty real vector, its feasibility means $0\leq b_i$ for every row, and the column conditions on $y$ are vacuous. This bundle defines the system, feasibility predicate and test; it contains no assertion that a particular system is infeasible or that a test input exists.
--
--   **Source and scope.** Primary §9 pp.21–24; Solovyev–Hales (2011), Efficient Formal Verification of Bounds of Linear Programs, §§2–3 pp.2–7; final more_arith/prove_lp.hl:215–228,339–349. Generic rational-system and multiplier semantics; no solver verdict is assumed.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9 pp.21–24; Solovyev–Hales (2011), Efficient Formal Verification of Bounds of Linear Programs, §§2–3 pp.2–7; final more_arith/prove_lp.hl:215–228,339–349. Generic rational-system and multiplier semantics; no solver verdict is assumed.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

/-
Flyspeck source material is reproduced and adapted under this license:
MIT License

Copyright (c) 2014 Thomas C. Hales

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open scoped BigOperators

namespace KeplerMission

/-- Rational linear inequalities, with real-valued feasible vectors. -/
structure RationalSystem (m n : ℕ) where
  matrix : Matrix (Fin m) (Fin n) ℚ
  rhs : Fin m → ℚ

def RationalSystem.Feasible {m n : ℕ} (S : RationalSystem m n) (x : Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, (S.matrix i j : ℝ) * x j ≤ (S.rhs i : ℝ)

/-- Exact Farkas-style nonnegative row multipliers, not a floating-point solver verdict.
Source interface: Hales et al. (2017), §9, published PDF pp. 23–24. -/
def RationalSystem.checkInfeasibility {m n : ℕ} (S : RationalSystem m n)
    (y : Fin m → ℚ) : Bool :=
  decide ((∀ i, 0 ≤ y i) ∧
    (∀ j, ∑ i, y i * S.matrix i j = 0) ∧ (∑ i, y i * S.rhs i) < 0)

end KeplerMission


