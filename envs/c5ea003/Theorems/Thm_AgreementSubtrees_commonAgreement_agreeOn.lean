-- Prove2me | Theorems.Thm_AgreementSubtrees_commonAgreement_agreeOn
-- name    : AgreementSubtrees.commonAgreement_agreeOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T20:59:43.79064+00:00
-- url     : https://prove2.me/theorems/60e2a1c2-e066-4dea-99ab-eff7f19ec69b
-- title:
--   A common agreement on `F` makes every two members of `F` agree.
-- statement:
--   A common agreement on `F` makes every two members of `F` agree.
--
--   ```lean
--   theorem AgreementSubtrees.commonAgreement_agreeOn{α ι : Type*} [DecidableEq α] {F : Finset ι}
--       {T : ι → SplitSystem α} {A : Finset α} (h : CommonAgreement F T A) :
--       ∀ i ∈ F, ∀ j ∈ F, AgreeOn (T i) (T j) A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Core.lean#L84

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

theorem AgreementSubtrees.commonAgreement_agreeOn{α ι : Type*} [DecidableEq α] {F : Finset ι}
    {T : ι → SplitSystem α} {A : Finset α} (h : CommonAgreement F T A) :
    ∀ i ∈ F, ∀ j ∈ F, AgreeOn (T i) (T j) A := by sorry
