-- Prove2me | Theorems.Thm_Catalog_EulerianNumbers_eul_row_sum
-- name    : Catalog.EulerianNumbers.eul_row_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:37:17.445839+00:00
-- url     : https://prove2.me/theorems/d0b84fd3-1855-4403-9379-855f73ed67b1
-- title:
--   Row-sum identity: for `n ≥ 1`, the `n`-th row sums to `n!`.
-- statement:
--   **Row-sum identity**: for `n ≥ 1`, the `n`-th row sums to `n!`.
--
--   ```lean
--   theorem Catalog.EulerianNumbers.eul_row_sum(n : ℕ) (hn : 1 ≤ n) :
--       ∑ k ∈ Finset.range n, eul n k = Nat.factorial n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/EulerianNumbers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/EulerianNumbers.lean#L55

-- Thm stub generated from Speculative/NumberTheory/EulerianNumbers.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_EulerianNumbers
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Eulerian numbers and the row-sum identity

The *Eulerian number* `A(n, k)` counts the permutations of `{1, …, n}` with exactly `k`
ascents.  Here we define a concrete recursive version `eul n k` and prove the classical
**row-sum identity**: for `n ≥ 1`,

`∑_{k = 0}^{n-1} eul n k = n!`.

The definition follows the standard triangular recurrence
`A(n+1, k+1) = (k+2) · A(n, k+1) + (n - k) · A(n, k)`,
with base row `A(0, 0) = 1` and left column `A(n, 0) = 1`.
-/

open Catalog.EulerianNumbers

open Finset

theorem Catalog.EulerianNumbers.eul_row_sum(n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, eul n k = Nat.factorial n := by sorry
