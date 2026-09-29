-- Prove2me | solution 1 for TwoTreeClosure.fst_follow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:44:10.793954+00:00
-- url     : https://prove2.me/submissions/cfcc6c51-ed8a-47c5-9931-062a23d8808b

-- Sol generated from Bridges/TwoTreeClosure/AscentWord.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_isNode_childA
import Theorems.Thm_TwoTreeClosure_isNode_childB
import Theorems.Thm_TwoTreeClosure_isNode_childC

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










/-! ### Depth versus magnitude: the tree is extremely unbalanced

Each branch multiplies the leading coordinate by at most `3`, so a word of length
`L` cannot reach beyond `3 ^ L`.  In the opposite direction the pure `A`-spine
increases the leading coordinate by exactly one per letter, so its depth grows like
the square root of the hypotenuse — the depth of a node is *not* logarithmic in `N`
in general.
-/

/-- Each branch at most triples the leading coordinate. -/
theorem fst_childOf_le {p : ℕ × ℕ} (l : Letter) (h : IsNode p.1 p.2) :
    (childOf l p).1 ≤ 3 * p.1 := by
  obtain ⟨hn, hnm, -, -⟩ := h
  cases l <;> simp only [childOf, childA, childB, childC] <;> omega






open TwoTreeClosure in
theorem solution{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w : List Letter, (follow w v).1 ≤ v.1 * 3 ^ w.length := by
  intro w
  induction w generalizing v with
  | nil => simp [follow]
  | cons l ls ih =>
      have h1 : (childOf l v).1 ≤ 3 * v.1 := fst_childOf_le l h
      have h2 := ih (childOf_isNode l h)
      simp only [follow, List.length_cons]
      calc (follow ls (childOf l v)).1 ≤ (childOf l v).1 * 3 ^ ls.length := h2
        _ ≤ (3 * v.1) * 3 ^ ls.length := by
            exact Nat.mul_le_mul_right _ h1
        _ = v.1 * 3 ^ (ls.length + 1) := by ring
