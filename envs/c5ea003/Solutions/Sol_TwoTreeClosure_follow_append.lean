-- Prove2me | solution 1 for TwoTreeClosure.follow_append
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:17.770314+00:00
-- url     : https://prove2.me/submissions/43d9ce2d-24b9-43e4-a7ce-4953779d44ef

-- Sol generated from Bridges/TwoTreeClosure/AscentWord.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

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













/-! ### Depth versus magnitude: the tree is extremely unbalanced

Each branch multiplies the leading coordinate by at most `3`, so a word of length
`L` cannot reach beyond `3 ^ L`.  In the opposite direction the pure `A`-spine
increases the leading coordinate by exactly one per letter, so its depth grows like
the square root of the hypotenuse — the depth of a node is *not* logarithmic in `N`
in general.
-/







open TwoTreeClosure in
theorem solution(v : ℕ × ℕ) (w : List Letter) (l : Letter) :
    follow (w ++ [l]) v = childOf l (follow w v) := by
  induction w generalizing v with
  | nil => rfl
  | cons a as ih => simpa [follow] using ih (childOf a v)
