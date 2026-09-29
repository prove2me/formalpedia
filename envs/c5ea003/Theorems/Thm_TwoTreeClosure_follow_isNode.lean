-- Prove2me | Theorems.Thm_TwoTreeClosure_follow_isNode
-- name    : TwoTreeClosure.follow_isNode
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:24.497497+00:00
-- url     : https://prove2.me/theorems/55098929-352e-4e55-b870-22f495674f28
-- title:
--   Follow isNode
-- statement:
--   Formal statement of `TwoTreeClosure.follow_isNode` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TwoTreeClosure.follow_isNode{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
--       ∀ w : List Letter, IsNode (follow w v).1 (follow w v).2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/AscentWord.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/AscentWord.lean#L61

-- Thm stub generated from Bridges/TwoTreeClosure/AscentWord.lean
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

theorem TwoTreeClosure.follow_isNode{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w : List Letter, IsNode (follow w v).1 (follow w v).2 := by sorry
