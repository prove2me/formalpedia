-- Prove2me | Definitions.Def_Combinatorics_FranklUnionClosed
-- name    : Combinatorics_FranklUnionClosed
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:29.583763+00:00
-- url     : https://prove2.me/theorems/05c8763a-de17-48c7-9da1-6b5f8aa8581a
-- title:
--   Aether Catalog definitions — Combinatorics_FranklUnionClosed
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.FranklUnionClosed`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/FranklUnionClosed.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.Frankl

open Finset

variable {α : Type*} [DecidableEq α]

/-- A family of finite sets is *union-closed* if it is closed under binary unions. -/
def IsUnionClosed (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- The sub-family of members of `F` that contain `x`. -/
def containing (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter (fun A => x ∈ A)

/-- `x` is *abundant* in `F` when it belongs to at least half of the members. -/
def Abundant (F : Finset (Finset α)) (x : α) : Prop :=
  F.card ≤ 2 * (containing F x).card

/-- Frankl's conjecture, stated for a single family `F`: there is an element of
some member that is abundant. -/
def FranklProperty (F : Finset (Finset α)) : Prop :=
  ∃ x, (∃ A ∈ F, x ∈ A) ∧ Abundant F x

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


end Catalog.Novelty.Frankl


