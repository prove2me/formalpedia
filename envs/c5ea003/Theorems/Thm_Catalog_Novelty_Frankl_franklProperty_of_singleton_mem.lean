-- Prove2me | Theorems.Thm_Catalog_Novelty_Frankl_franklProperty_of_singleton_mem
-- name    : Catalog.Novelty.Frankl.franklProperty_of_singleton_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:05.558957+00:00
-- url     : https://prove2.me/theorems/91d23ff1-6712-41fd-8db4-fb6516cace53
-- title:
--   Existence form of Frankl's conjecture in the singleton case.
-- statement:
--   Existence form of Frankl's conjecture in the singleton case.
--
--   ```lean
--   theorem Catalog.Novelty.Frankl.franklProperty_of_singleton_mem(F : Finset (Finset α))
--       (hF : IsUnionClosed F) (a : α) (ha : ({a} : Finset α) ∈ F) :
--       FranklProperty F := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/FranklUnionClosed.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/FranklUnionClosed.lean#L101

-- Thm stub generated from Combinatorics/FranklUnionClosed.lean
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

theorem Catalog.Novelty.Frankl.franklProperty_of_singleton_mem(F : Finset (Finset α))
    (hF : IsUnionClosed F) (a : α) (ha : ({a} : Finset α) ∈ F) :
    FranklProperty F := by sorry
