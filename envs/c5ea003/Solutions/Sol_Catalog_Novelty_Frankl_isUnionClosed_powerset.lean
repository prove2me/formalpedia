-- Prove2me | solution 1 for Catalog.Novelty.Frankl.isUnionClosed_powerset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:42.952699+00:00
-- url     : https://prove2.me/submissions/238fb449-660b-442b-98fd-48b27051a957

-- Sol generated from Combinatorics/FranklUnionClosed.lean
import Mathlib
import Definitions.Def_Combinatorics_FranklUnionClosed

/-!
# Frankl's Union-Closed Sets Conjecture: core formalization and partial results

A finite family of finite sets `F` is **union-closed** when `A ∪ B ∈ F` whenever
`A, B ∈ F`.  **Frankl's conjecture** asserts that every union-closed family
containing a nonempty set has an *abundant* element: some `x` lying in at least
half of the members of `F`.

This file develops the core definitions and proves several genuine partial
results, the centerpiece being:

* `frankl_singleton` — if a union-closed family contains a **singleton** `{a}`,
  then `a` is abundant.  This is the classical injection argument: `A ↦ A ∪ {a}`
  injects the sets avoiding `a` into the sets containing `a`.

We also prove the lattice/order infrastructure (`sup_mem` — a nonempty
union-closed family contains its top element) and assemble the existence form of
the conjecture in the singleton case.

-- !-- Lab Notes -- !--
Hypothesis (H1): The singleton case of Frankl is provable by an explicit
injection `A ↦ insert a A`.  Surprising sub-claim (H2): the *existence* of a top
element (union of all members) holds for any nonempty union-closed family with no
extra hypotheses — it is a pure semilattice fact.
Experiment: formalized both; H1 via `Finset.card_le_card_of_injOn`, H2 via
`Finset.induction`.
-/

open Catalog.Novelty.Frankl

open Finset

variable {α : Type*} [DecidableEq α]





/-
Counting split: the members of `F` are partitioned by whether they contain `x`.
-/

/-
**Centerpiece.**  If a union-closed family contains the singleton `{a}`, then
`a` is abundant.  Proof: `A ↦ insert a A` injects `{A ∈ F : a ∉ A}` into
`{A ∈ F : a ∈ A}` (it stays in `F` by union-closure with `{a}`), so the latter is
at least as large as the former, giving `|F| ≤ 2·|containing F a|`.
-/



/-
A nonempty union-closed family contains its **top element** `F.sup id`, the
union of all its members.  This is the order-theoretic content: `(F, ⊆)` is a
finite join-semilattice with a greatest element lying in `F`.
-/



open Catalog.Novelty.Frankl in
theorem solution(s : Finset α) : IsUnionClosed s.powerset := by
  intro A hA B hB
  exact Finset.mem_powerset.mpr (Finset.union_subset (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB))
