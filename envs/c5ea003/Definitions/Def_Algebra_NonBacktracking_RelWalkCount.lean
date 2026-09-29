-- Prove2me | Definitions.Def_Algebra_NonBacktracking_RelWalkCount
-- name    : Algebra_NonBacktracking_RelWalkCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:22:13.838881+00:00
-- url     : https://prove2.me/theorems/2872405e-41a4-4699-86ef-a41a017e60de
-- title:
--   Aether Catalog definitions — Algebra_NonBacktracking_RelWalkCount
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NonBacktracking.RelWalkCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NonBacktracking/RelWalkCount.lean by skeleton subtraction
import Mathlib

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

namespace RelWalkCount


variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop) [DecidableRel r]

/-- The 0-1 matrix (over `ℕ`) of a decidable relation. -/
def relMatrix : Matrix ι ι ℕ := Matrix.of fun i j => if r i j then 1 else 0


/-- `walks r n a b` is the finset of walks of length `n` from `a` to `b`, encoded as
lists of `n + 1` elements, in the digraph with arc relation `r`. -/
def walks : ℕ → ι → ι → Finset (List ι)
  | 0, a, b => if a = b then {[a]} else ∅
  | n + 1, a, b =>
      (univ.filter fun c => r a c).biUnion fun c => (walks n c b).image (fun l => a :: l)







/-- The finset of **rooted closed walks** of length `n`: walks of length `n` whose
initial and final vertex coincide. The root is the (marked) initial vertex. -/
def closedWalks (n : ℕ) : Finset (List ι) := univ.biUnion fun a => walks r n a a



/-! ### Row sums -/



end RelWalkCount


