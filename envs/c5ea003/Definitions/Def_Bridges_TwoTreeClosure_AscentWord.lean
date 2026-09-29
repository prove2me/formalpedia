-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_AscentWord
-- name    : Bridges_TwoTreeClosure_AscentWord
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:00.023356+00:00
-- url     : https://prove2.me/theorems/1ba36345-4346-48ce-bdf7-7c3b65ca109a
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_AscentWord
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.AscentWord`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/AscentWord.lean by skeleton subtraction
import Mathlib
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

namespace TwoTreeClosure

/-- Apply the branch named by a letter. -/
def childOf : Letter → ℕ × ℕ → ℕ × ℕ
  | Letter.A, p => childA p.1 p.2
  | Letter.B, p => childB p.1 p.2
  | Letter.C, p => childC p.1 p.2

/-- Read a word as a descent starting from a node. -/
def follow : List Letter → ℕ × ℕ → ℕ × ℕ
  | [], v => v
  | l :: ls, v => follow ls (childOf l v)











/-! ### Depth versus magnitude: the tree is extremely unbalanced

Each branch multiplies the leading coordinate by at most `3`, so a word of length
`L` cannot reach beyond `3 ^ L`.  In the opposite direction the pure `A`-spine
increases the leading coordinate by exactly one per letter, so its depth grows like
the square root of the hypotenuse — the depth of a node is *not* logarithmic in `N`
in general.
-/






end TwoTreeClosure


