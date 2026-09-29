-- Prove2me | Theorems.Thm_Catalog_Novelty_Frankl_frankl_singleton
-- name    : Catalog.Novelty.Frankl.frankl_singleton
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:08:45.126066+00:00
-- url     : https://prove2.me/theorems/1d18962b-ed3c-459a-b7dd-5e13c7bc2093
-- title:
--   Frankl singleton
-- statement:
--   Formal statement of `Catalog.Novelty.Frankl.frankl_singleton` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.Frankl.frankl_singleton(F : Finset (Finset α)) (hF : IsUnionClosed F)
--       (a : α) (ha : ({a} : Finset α) ∈ F) : Abundant F a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FranklUnionClosed.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FranklUnionClosed.lean#L67

-- Thm stub generated from Novelty/FranklUnionClosed.lean
import Mathlib
import Definitions.Def_Novelty_FranklUnionClosed

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

theorem Catalog.Novelty.Frankl.frankl_singleton(F : Finset (Finset α)) (hF : IsUnionClosed F)
    (a : α) (ha : ({a} : Finset α) ∈ F) : Abundant F a := by sorry
