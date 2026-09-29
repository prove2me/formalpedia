-- Prove2me | Theorems.Thm_RelWalkCount_rowSum_pow
-- name    : RelWalkCount.rowSum_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:09.099532+00:00
-- url     : https://prove2.me/theorems/4db7d923-9225-4d9c-8d27-d545c0fd352c
-- title:
--   If every row of `relMatrix r` sums to `q`, then every row of its `n`-th power sums
-- statement:
--   If every row of `relMatrix r` sums to `q`, then every row of its `n`-th power sums
--   to `q ^ n`.
--
--   ```lean
--   theorem RelWalkCount.rowSum_pow{q : ℕ} (hq : ∀ a : ι, ∑ b, relMatrix r a b = q) :
--       ∀ (n : ℕ) (a : ι), ∑ b, (relMatrix r ^ n) a b = q ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/RelWalkCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/RelWalkCount.lean#L235

-- Thm stub generated from Algebra/NonBacktracking/RelWalkCount.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount

/-!
# Counting walks in a digraph by powers of its 0-1 matrix

This file develops, from scratch, the combinatorial interpretation of the entries and
the trace of powers of the incidence (0-1) matrix of an *arbitrary* decidable relation
`r : ι → ι → Prop` on a finite type `ι`.

Mathlib provides such a statement only for the adjacency matrix of a `SimpleGraph`
(`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`).  The relation we ultimately care
about — "arc `f` follows arc `e` without backtracking" — is **not symmetric**, so the
`SimpleGraph` machinery does not apply and the theory has to be redone for a general
directed relation.

## Main definitions

* `RelWalkCount.relMatrix r` — the 0-1 matrix of `r` over `ℕ`.
* `RelWalkCount.walks r n a b` — the finset of walks of length `n` (i.e. lists of
  `n + 1` vertices) from `a` to `b` all of whose consecutive pairs are `r`-related.
* `RelWalkCount.closedWalks r n` — the finset of *rooted closed* walks of length `n`:
  walks of length `n` whose first and last entry agree.

## Main results

* `RelWalkCount.mem_walks` — the recursive definition of `walks` really describes the
  set of `r`-chains of the prescribed length and endpoints.
* `RelWalkCount.relMatrix_pow_apply` — `(M ^ n) a b` is the number of walks from `a`
  to `b` of length `n`.
* `RelWalkCount.trace_relMatrix_pow` — `trace (M ^ n)` is the number of rooted closed
  walks of length `n`.
* `RelWalkCount.rowSum_pow` — if every row of `M` sums to `q`, then every row of
  `M ^ n` sums to `q ^ n`; consequently `trace (M ^ n) ≤ card ι * q ^ n`.
-/

open Finset Matrix

open RelWalkCount


variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop) [DecidableRel r]













/-! ### Row sums -/

theorem RelWalkCount.rowSum_pow{q : ℕ} (hq : ∀ a : ι, ∑ b, relMatrix r a b = q) :
    ∀ (n : ℕ) (a : ι), ∑ b, (relMatrix r ^ n) a b = q ^ n := by sorry
