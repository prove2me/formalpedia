-- Prove2me | Theorems.Thm_Erdos390_prime_power_column_degree_le_log
-- name    : Erdos390.prime_power_column_degree_le_log
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T14:00:36.872053+00:00
-- url     : https://prove2.me/theorems/8dbd7959-51fe-42a8-aa66-a55585b591c5
-- title:
--   Logarithmic degree of prime-power divisibility columns
-- statement:
--   Let $0<a\le M$ be natural numbers. A column is a prime power $p^j\le M$ with $j\ge1$, and it contains $a$ when $p^j\mid a$. Then
--
--   $$\#\{(p,j):p\text{ prime},\ j\ge1,\ p^j\le M,\ p^j\mid a\}\le\lfloor\log_2 M\rfloor.$$
--
--   This supplies the column-degree bound for deterministic rounding of positive integer factors. All prime powers, including repeated powers of the same prime, are counted.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, equations rounding-prime-power-column, rounding-column-degree, rounding-error-box, and rounding-no-rough-error. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex; corresponding Lean files PrimePowerColumns.lean, ValuationError.lean and GuardedExactificationAlgebra.lean.

import Definitions.Def_erdos390_prime_power_rounding
open scoped BigOperators
open Erdos390.WholePaper

theorem Erdos390.prime_power_column_degree_le_log
    {M a : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    (columnsContaining (Finset.univ : Finset ↥(primePowerColumns M))
      (primePowerInc M) a).card ≤ Nat.log 2 M := by sorry
