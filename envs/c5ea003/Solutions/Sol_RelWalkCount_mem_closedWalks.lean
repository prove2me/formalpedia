-- Prove2me | solution 1 for RelWalkCount.mem_closedWalks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:37:11.197789+00:00
-- url     : https://prove2.me/submissions/4d8d5944-4178-4ef8-ac9a-666391c15d13

-- Sol generated from Algebra/NonBacktracking/RelWalkCount.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Theorems.Thm_RelWalkCount_mem_walks

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




open RelWalkCount in
theorem solution(n : ℕ) (l : List ι) :
    l ∈ closedWalks r n ↔
      l.length = n + 1 ∧ List.IsChain r l ∧ l.head? = l.getLast? := by
  simp only [closedWalks, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hlen, hhead, hlast, hchain⟩ := (mem_walks r n a a l).1 ha
    exact ⟨hlen, hchain, by rw [hhead, hlast]⟩
  · rintro ⟨hlen, hchain, hhl⟩
    have hne : l ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    obtain ⟨a, ha⟩ : ∃ a, l.head? = some a := by
      cases l with
      | nil => exact absurd rfl hne
      | cons x t => exact ⟨x, rfl⟩
    exact ⟨a, (mem_walks r n a a l).2 ⟨hlen, ha, by rw [← hhl]; exact ha, hchain⟩⟩
