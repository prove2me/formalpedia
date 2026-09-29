-- Prove2me | Definitions.Def_Combinatorics_Core
-- name    : Combinatorics_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:30:25.043352+00:00
-- url     : https://prove2.me/theorems/d57d0f51-cc9e-4e5a-932a-a8f29b749da4
-- title:
--   Aether Catalog definitions — Combinatorics_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Core.lean by skeleton subtraction
import Mathlib
/-
# Core definitions for agreement subtrees of phylogenetic trees

NOTE (restored module).  `Novelty/AgreementSubtreesMultiple.lean` and
`Novelty/AgreementSubtreesCounting.lean` are written against this module, which was missing
from the catalogue, so neither of them compiled.  This file restores the four basic notions
they use: split systems, their restriction to a retained leaf set, agreement of two trees on a
leaf set, and common agreement of a whole family.

A phylogenetic tree on a leaf set is recorded by the finite family of *split sides* it
displays; restricting the tree to a subset `A` of the leaves intersects every displayed split
with `A`.  Agreement of two trees on `A` then means that they display the same splits after
restriction.
-/

open Finset

namespace AgreementSubtrees

/-- A **split system**: the finite family of split sides displayed by a phylogenetic tree on a
leaf set of type `α`. -/
abbrev SplitSystem (α : Type*) : Type _ := Finset (Finset α)

/-- **Restriction** of a split system to the retained leaf set `A`: every displayed split side
is intersected with `A`. -/
def restrict {α : Type*} [DecidableEq α] (T : SplitSystem α) (A : Finset α) : SplitSystem α :=
  T.image (fun s => s ∩ A)

/-- Two trees **agree on** the leaf set `A` when their restrictions to `A` coincide. -/
def AgreeOn {α : Type*} [DecidableEq α] (T U : SplitSystem α) (A : Finset α) : Prop :=
  restrict T A = restrict U A

/-- A family `F` of trees has a **common agreement subtree** on `A`: all the trees indexed by
`F` restrict to one and the same split system on `A`. -/
def CommonAgreement {α ι : Type*} [DecidableEq α] (F : Finset ι) (T : ι → SplitSystem α)
    (A : Finset α) : Prop :=
  ∃ R : SplitSystem α, ∀ i ∈ F, restrict (T i) A = R






/-- `IsAgreementThreshold m k n` says that any `k` phylogenetic trees on a common leaf set of
at least `m` leaves admit a common agreement subtree on at least `n` leaves. -/
def IsAgreementThreshold (m k n : ℕ) : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : Finset α) (T : Fin k → SplitSystem α),
    m ≤ L.card → ∃ A ⊆ L, n ≤ A.card ∧ CommonAgreement (Finset.univ : Finset (Fin k)) T A



end AgreementSubtrees


