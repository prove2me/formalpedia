-- Prove2me | solution 1 for TwoTreeClosure.follow_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:44:10.246767+00:00
-- url     : https://prove2.me/submissions/47dd725d-4af8-475e-8409-7f5180cb9c52

-- Sol generated from Bridges/TwoTreeClosure/AscentWord.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_follow_append
import Theorems.Thm_TwoTreeClosure_follow_isNode
import Theorems.Thm_TwoTreeClosure_isNode_childA
import Theorems.Thm_TwoTreeClosure_isNode_childB
import Theorems.Thm_TwoTreeClosure_isNode_childC
import Theorems.Thm_TwoTreeClosure_letterOf_childOf
import Theorems.Thm_TwoTreeClosure_parentP_childA
import Theorems.Thm_TwoTreeClosure_parentP_childB
import Theorems.Thm_TwoTreeClosure_parentP_childC

/-!
# The ascent word is a normal form

`Bridges.TwoTreeClosure.TreeCore` proves that every arithmetic node is reachable
from the root and that each node remembers the branch that produced it
(`parentP_child*`, `letterOf_child*`).  Here that is upgraded to a **normal form**:

* `follow` reads a word in `{A, B, C}` as a descent from a node;
* `follow_injective` : distinct words reach distinct nodes, for every starting node;
* `ascent_word_normal_form` : words in `{A, B, C}` are in bijection with the nodes of
  the subtree below a fixed node, so every node of the Berggren/Price tree carries a
  unique ascent word — the tree is free on its three generators.

This is the structural statement behind the "positional content" of the two-tree
question: the letters of the word are exactly the information that the blindness
theorems of `TreeCore` show to be unreadable from `N`.
-/

open TwoTreeClosure



theorem childOf_isNode {p : ℕ × ℕ} (l : Letter) (h : IsNode p.1 p.2) :
    IsNode (childOf l p).1 (childOf l p).2 := by
  cases l
  · exact isNode_childA h
  · exact isNode_childB h
  · exact isNode_childC h


theorem parentP_childOf {p : ℕ × ℕ} (l : Letter) (h : IsNode p.1 p.2) :
    parentP (childOf l p) = p := by
  cases l
  · simpa using parentP_childA h
  · simpa using parentP_childB h
  · simpa using parentP_childC h

/-- Each branch strictly increases the leading coordinate. -/
theorem fst_lt_childOf {p : ℕ × ℕ} (l : Letter) (h : IsNode p.1 p.2) :
    p.1 < (childOf l p).1 := by
  obtain ⟨hn, hnm, -, -⟩ := h
  cases l <;> simp only [childOf, childA, childB, childC] <;> omega



theorem fst_le_follow {v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w : List Letter, v.1 ≤ (follow w v).1 := by
  intro w
  induction w generalizing v with
  | nil => exact le_rfl
  | cons l ls ih =>
      have h1 : v.1 < (childOf l v).1 := fst_lt_childOf l h
      have h2 := ih (childOf_isNode l h)
      simp only [follow]
      omega




/-! ### Depth versus magnitude: the tree is extremely unbalanced

Each branch multiplies the leading coordinate by at most `3`, so a word of length
`L` cannot reach beyond `3 ^ L`.  In the opposite direction the pure `A`-spine
increases the leading coordinate by exactly one per letter, so its depth grows like
the square root of the hypotenuse — the depth of a node is *not* logarithmic in `N`
in general.
-/







open TwoTreeClosure in
theorem solution{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w w' : List Letter, follow w v = follow w' v → w = w' := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro w' hw
      rcases List.eq_nil_or_concat w' with rfl | ⟨u, l, rfl⟩
      · rfl
      · exfalso
        rw [List.concat_eq_append, follow_append] at hw
        have h1 : v.1 ≤ (follow u v).1 := fst_le_follow h u
        have h2 : (follow u v).1 < (childOf l (follow u v)).1 :=
          fst_lt_childOf l (follow_isNode h u)
        have : (follow [] v).1 = v.1 := rfl
        rw [← hw] at h2
        simp only [follow] at h2
        omega
  | append_singleton u a ih =>
      intro w' hw
      rcases List.eq_nil_or_concat w' with rfl | ⟨u', l', rfl⟩
      · exfalso
        rw [follow_append] at hw
        have h1 : v.1 ≤ (follow u v).1 := fst_le_follow h u
        have h2 : (follow u v).1 < (childOf a (follow u v)).1 :=
          fst_lt_childOf a (follow_isNode h u)
        rw [hw] at h2
        simp only [follow] at h2
        omega
      · rw [List.concat_eq_append] at hw ⊢
        rw [follow_append, follow_append] at hw
        have hu : IsNode (follow u v).1 (follow u v).2 := follow_isNode h u
        have hu' : IsNode (follow u' v).1 (follow u' v).2 := follow_isNode h u'
        have hletter : a = l' := by
          have e1 := letterOf_childOf a hu
          have e2 := letterOf_childOf l' hu'
          rw [hw, e2] at e1
          exact e1.symm
        have hparent : follow u v = follow u' v := by
          have e1 := parentP_childOf a hu
          have e2 := parentP_childOf l' hu'
          rw [← e1, hw, e2]
        rw [hletter, ih u' hparent]
