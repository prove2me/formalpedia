-- Prove2me | Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_pellP_two_mul
-- name    : Catalog.Novelty.PellSpine.pellQ_dvd_pellP_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:14:48.859989+00:00
-- url     : https://prove2.me/theorems/460738ed-d080-4bc4-99e9-319781c23bc1
-- title:
--   `Q n` divides `P (2n)`: doubling always produces a factor of the companion term.
-- statement:
--   `Q n` divides `P (2n)`: doubling always produces a factor of the companion term.
--
--   ```lean
--   theorem Catalog.Novelty.PellSpine.pellQ_dvd_pellP_two_mul(n : ℕ) : pellQ n ∣ pellP (2 * n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PellSpineDivisibility.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PellSpineDivisibility.lean#L111

-- Thm stub generated from Novelty/PellSpineDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
/-
# Strong divisibility on the Pell spine — and four conjectures it kills

Building on `Novelty.PellSpineCore`, this file proves that the Pell numbers form a
**strong divisibility sequence**,

`gcd (P m) (P n) = P (gcd m n)`,

and then uses that theorem as a *falsification engine*: four natural strengthenings of
it are each destroyed by a single explicit counterexample, all of them living inside the
first eight Pell numbers.

## Proved

* `pellP_gcd_step`   — the Euclidean step `gcd (P (m+n)) (P n) = gcd (P m) (P n)`;
* `pellP_gcd`        — **strong divisibility** `gcd (P m) (P n) = P (gcd m n)`;
* `pellP_dvd_iff`    — `m ∣ n ↔ P m ∣ P n`, with no side condition at all;
* `pellP_prime_index`— if `P n` is prime then `n` is prime;
* `pellQ_dvd_odd_multiple` — the *guarded* companion statement `Q n ∣ Q ((2k+1) * n)`.

## Refuted (each by one counterexample)

* `not_pellP_prime_of_prime_index`  — `n` prime does **not** force `P n` prime: `P 7 = 169 = 13²`;
* `not_pellP_squarefree`            — Pell numbers are **not** all squarefree: again `P 7 = 13²`
  (the exact analogue for Fibonacci numbers is a well-known open problem, and here it is
  false at the seventh term);
* `not_pellQ_strong_divisibility`   — the companion sequence is **not** a strong divisibility
  sequence: `gcd (Q 3) (Q 6) = gcd 7 99 = 1 ≠ 7 = Q 3`, even though `3 ∣ 6`;
* `not_prime_dvd_pellP_pred`        — the naive Fermat-style law `p ∣ P (p-1)` fails: `3 ∤ P 2 = 2`
  (the correct exponent is `p - (2/p)`, and `2` is a non-residue mod `3`).

The moral, extracted in `FUTURE_DIRECTIONS.md`: strong divisibility is a property of the
*norm-form solution* sequence `P`, not of the *trace* sequence `Q`, and it degrades to a
`2k+1`-graded statement on `Q`.
-/

open Catalog.Novelty.PellSpine

/-! ## The Euclidean step -/



/-! ## Strong divisibility -/




/-! ## The guarded companion statement -/

theorem Catalog.Novelty.PellSpine.pellQ_dvd_pellP_two_mul(n : ℕ) : pellQ n ∣ pellP (2 * n) := by sorry
