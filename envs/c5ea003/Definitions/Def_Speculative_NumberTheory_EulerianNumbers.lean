-- Prove2me | Definitions.Def_Speculative_NumberTheory_EulerianNumbers
-- name    : Speculative_NumberTheory_EulerianNumbers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:39.121493+00:00
-- url     : https://prove2.me/theorems/393e0c9f-15a4-4c23-b48a-0aba76215898
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_EulerianNumbers
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.EulerianNumbers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/EulerianNumbers.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.EulerianNumbers

open Finset

/-- The Eulerian numbers, defined by the triangular recurrence. -/
def eul : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, (_ + 1) => 0
  | (_ + 1), 0 => 1
  | (n + 1), (k + 1) => (k + 2) * eul n (k + 1) + (n - k) * eul n k









end Catalog.EulerianNumbers


