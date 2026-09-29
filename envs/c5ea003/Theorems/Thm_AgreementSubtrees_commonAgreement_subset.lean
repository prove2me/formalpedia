-- Prove2me | Theorems.Thm_AgreementSubtrees_commonAgreement_subset
-- name    : AgreementSubtrees.commonAgreement_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T20:59:53.461143+00:00
-- url     : https://prove2.me/theorems/8f9989d6-806e-4aa4-81c2-711ce9e3bee2
-- title:
--   Common agreement is inherited by smaller leaf sets.
-- statement:
--   Common agreement is inherited by smaller leaf sets.
--
--   ```lean
--   theorem AgreementSubtrees.commonAgreement_subset{α ι : Type*} [DecidableEq α] {F : Finset ι}
--       {T : ι → SplitSystem α} {A A' : Finset α} (h : A' ⊆ A) (hc : CommonAgreement F T A) :
--       CommonAgreement F T A' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Core.lean#L60

-- Thm stub generated from Combinatorics/Core.lean
import Mathlib
import Definitions.Def_Combinatorics_Core
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

open AgreementSubtrees

theorem AgreementSubtrees.commonAgreement_subset{α ι : Type*} [DecidableEq α] {F : Finset ι}
    {T : ι → SplitSystem α} {A A' : Finset α} (h : A' ⊆ A) (hc : CommonAgreement F T A) :
    CommonAgreement F T A' := by sorry
