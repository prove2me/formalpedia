-- Prove2me | Definitions.Def_Novelty_Counting
-- name    : Novelty_Counting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:03.006633+00:00
-- url     : https://prove2.me/theorems/9304d3f4-befe-4406-8d2e-fa212f6afa63
-- title:
--   Aether Catalog definitions — Novelty_Counting
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Counting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Counting.lean by skeleton subtraction
import Mathlib

/-!
# Proof Space I: Counting statements

We model *proof space* as the set of finite strings ("statements") over a fixed
finite alphabet with `k ≥ 2` symbols.  A statement of *length* `i` is a word of
`i` symbols, so there are exactly `k ^ i` statements of length `i`, and

  `S k n = ∑_{i=0}^{n} k ^ i`

statements of length `≤ n`.  This file records the basic combinatorics of the
proof space: the closed (geometric) form of `S`, its exponential growth, and the
asymptotic proportion occupied by the top length.  These facts are the
scaffolding for the order-parameter and dimension analyses in the companion
files.
-/

namespace ProofSpace

open Finset


/-- `S k n` is the number of statements of length `≤ n`, i.e. `∑_{i=0}^{n} k^i`. -/
def S (k n : ℕ) : ℕ := ∑ i ∈ range (n + 1), k ^ i





end ProofSpace


