-- Prove2me | Theorems.Thm_RelWalkCount_getLast_q_cons_of_ne_nil
-- name    : RelWalkCount.getLast_q_cons_of_ne_nil
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T23:38:53.681524+00:00
-- url     : https://prove2.me/theorems/3b1665ae-e342-4643-971c-0e7175b8431e
-- title:
--   `getLast?` ignores a prepended element as long as the tail is nonempty.
-- statement:
--   `getLast?` ignores a prepended element as long as the tail is nonempty.
--
--   ```lean
--   theorem RelWalkCount.getLast?_cons_of_ne_nil{α : Type*} (a : α) {l : List α} (h : l ≠ []) :
--       (a :: l).getLast? = l.getLast? := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/RelWalkCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/RelWalkCount.lean#L39

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

theorem RelWalkCount.getLast_q_cons_of_ne_nil{α : Type*} (a : α) {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by sorry
