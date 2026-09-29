-- Prove2me | solution 1 for AgreementSubtrees.commonAgreement_subset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:39:48.389819+00:00
-- url     : https://prove2.me/submissions/6a093d86-a216-4c54-8b7e-c742964d1ddb

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








/-- Restricting twice is restricting once, provided the second leaf set is contained in the
first. -/
theorem restrict_restrict {α : Type*} [DecidableEq α] (T : SplitSystem α) {A A' : Finset α}
    (h : A' ⊆ A) : AgreementSubtrees.restrict (AgreementSubtrees.restrict T A) A' = AgreementSubtrees.restrict T A' := by
  unfold AgreementSubtrees.restrict
  rw [Finset.image_image]
  refine Finset.image_congr fun s _ => ?_
  simp only [Function.comp_apply, Finset.inter_assoc, Finset.inter_eq_right.mpr h]






open AgreementSubtrees in
theorem solution{α ι : Type*} [DecidableEq α] {F : Finset ι}
    {T : ι → SplitSystem α} {A A' : Finset α} (h : A' ⊆ A) (hc : CommonAgreement F T A) :
    CommonAgreement F T A' := by
  obtain ⟨R, hR⟩ := hc
  refine ⟨AgreementSubtrees.restrict R A', fun i hi => ?_⟩
  rw [← restrict_restrict (T i) h, hR i hi]
