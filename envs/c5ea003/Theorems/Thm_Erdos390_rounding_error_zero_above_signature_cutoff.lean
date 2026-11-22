-- Prove2me | Theorems.Thm_Erdos390_rounding_error_zero_above_signature_cutoff
-- name    : Erdos390.rounding_error_zero_above_signature_cutoff
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T14:00:41.683627+00:00
-- url     : https://prove2.me/theorems/9330d073-1946-4629-905a-cf65bf322951
-- title:
--   Exact signature rows eliminate every large-prime rounding error
-- statement:
--   Let a finite candidate set $A$ be assigned to rows, and let $a_i$ be its integer values. Fix a cutoff $y$. Assume every row has a fixed complete rough signature, namely the vector $(v_q(a_i))_{q>y}$. If two real vectors $X,x$ have equal total weight on every row, then
--
--   $$\sum_{i\in A}(X_i-x_i)v_q(a_i)=0\qquad(q>y).$$
--
--   Thus the correction bank needs to address only primes at most $y$. Preserving complete signatures retains prime-power multiplicities as well as the primes themselves.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, equations rounding-prime-power-column, rounding-column-degree, rounding-error-box, and rounding-no-rough-error. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex; corresponding Lean files PrimePowerColumns.lean, ValuationError.lean and GuardedExactificationAlgebra.lean.

import Definitions.Def_erdos390_prime_power_rounding
open scoped BigOperators
open Erdos390.WholePaper

theorem Erdos390.rounding_error_zero_above_signature_cutoff
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (value : A → ℕ) (y : ℕ) (X x : A → ℝ)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    {q : ℕ} (hyq : y < q) :
    roundingValuationError value X x q = 0 := by sorry
