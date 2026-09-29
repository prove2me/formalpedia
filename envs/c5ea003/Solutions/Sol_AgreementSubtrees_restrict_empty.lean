-- Prove2me | solution 1 for AgreementSubtrees.restrict_empty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:26:14.672564+00:00
-- url     : https://prove2.me/submissions/281de6a8-fde5-4624-b57f-94f72983a782

-- Sol generated from Probability/Core.lean
import Mathlib
import Definitions.Def_Probability_Core

/-!
# Agreement subtrees: restriction and threshold infrastructure

A finite unrooted phylogenetic tree is determined by its nontrivial edge splits. This
file isolates the restriction algebra used in the multiple-tree maximum-agreement-
subtree problem. A `SplitSystem α` is represented extensionally as a finite family of
finite leaf sets (one consistently chosen side of each split). Restriction to a leaf set
intersects every split with that set. The results therefore apply more generally to
arbitrary finite split systems.

The principal structural theorem, `commonAgreement_iff_pairwise`, says that a leaf set
is a common agreement set for a nonempty family exactly when every pair of systems has
identical restriction there. We also prove heredity under taking smaller leaf sets and
the abstract transfer from any common-subtree threshold to a common-quartet threshold.
-/

open Finset

open AgreementSubtrees

variable {α ι : Type*} [DecidableEq α]




















/-
No agreement threshold can request more leaves than the ambient leaf set contains.
-/

/-
For one tree, the exact threshold condition is simply that the requested leaf set
fits in the ambient leaf set. This is the base case of the multiple-tree problem.
-/


open AgreementSubtrees in
@[simp] theorem solution(T : SplitSystem α) : restrict T ∅ = {∅} ∨ T = ∅ := by
  by_cases h : T = ∅
  · exact Or.inr h
  · left
    ext x
    constructor
    · intro hx
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
      simp
    · intro hx
      have hnonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨s, hs⟩ := hnonempty
      simp only [Finset.mem_singleton] at hx
      subst x
      exact Finset.mem_image.mpr ⟨s, hs, by simp⟩
