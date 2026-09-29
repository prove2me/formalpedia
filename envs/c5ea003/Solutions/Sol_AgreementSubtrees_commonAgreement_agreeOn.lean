-- Prove2me | solution 1 for AgreementSubtrees.commonAgreement_agreeOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:37:13.689161+00:00
-- url     : https://prove2.me/submissions/63765c40-4edb-4840-861a-75b17ee1ba3b

-- Sol generated from Combinatorics/Core.lean
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














open AgreementSubtrees in
theorem solution{α ι : Type*} [DecidableEq α] {F : Finset ι}
    {T : ι → SplitSystem α} {A : Finset α} (h : CommonAgreement F T A) :
    ∀ i ∈ F, ∀ j ∈ F, AgreeOn (T i) (T j) A := by
  obtain ⟨R, hR⟩ := h
  exact fun i hi j hj => by rw [AgreeOn, hR i hi, hR j hj]
