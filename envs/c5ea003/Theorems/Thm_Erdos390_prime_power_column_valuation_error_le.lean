-- Prove2me | Theorems.Thm_Erdos390_prime_power_column_valuation_error_le
-- name    : Erdos390.prime_power_column_valuation_error_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T14:00:25.961331+00:00
-- url     : https://prove2.me/theorems/9aa0db4b-852f-4307-9b21-459e25c30fd3
-- title:
--   Prime-valuation error from prime-power column discrepancy
-- statement:
--   Let $A$ be finite, $M>0$, and $a_i\in\{1,\ldots,M\}$. Let $X_i,x_i\in\mathbb R$. Suppose every prime-power divisibility column has discrepancy at most $4d$. Then for every prime $p$,
--
--   $$\left|\sum_{i\in A}(X_i-x_i)v_p(a_i)\right|\le4d\lfloor\log_p M\rfloor.$$
--
--   This converts the finite incidence discrepancy estimate into the valuation-error budget used by the correction bank. The conclusion holds for arbitrary real vectors satisfying the column bound.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, equations rounding-prime-power-column, rounding-column-degree, rounding-error-box, and rounding-no-rough-error. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex; corresponding Lean files PrimePowerColumns.lean, ValuationError.lean and GuardedExactificationAlgebra.lean.

import Definitions.Def_erdos390_prime_power_rounding
open scoped BigOperators
open Erdos390.WholePaper

theorem Erdos390.prime_power_column_valuation_error_le
    {A : Type*} [Fintype A]
    (value : A → ℕ) (M d : ℕ) (X x : A → ℝ)
    (hM : 0 < M)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hcolumn : ∀ q : ↥(primePowerColumns M),
      |∑ a, (X a - x a) *
        zeroOneColumn
          (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
        (4 * d : ℝ))
    {p : ℕ} (hp : p.Prime) :
    |roundingValuationError value X x p| ≤
      (4 * d * Nat.log p M : ℝ) := by sorry
