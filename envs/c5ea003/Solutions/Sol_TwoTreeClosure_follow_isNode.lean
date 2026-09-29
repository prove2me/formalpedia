-- Prove2me | solution 1 for TwoTreeClosure.follow_isNode
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:18.301405+00:00
-- url     : https://prove2.me/submissions/d7584b7c-670b-43c4-b25d-bbf251c8b393

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







open TwoTreeClosure in
theorem solution{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w : List Letter, IsNode (follow w v).1 (follow w v).2 := by
  intro w
  induction w generalizing v with
  | nil => exact h
  | cons l ls ih => exact ih (childOf_isNode l h)
