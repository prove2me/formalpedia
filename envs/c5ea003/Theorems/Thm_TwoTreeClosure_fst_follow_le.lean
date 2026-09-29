-- Prove2me | Theorems.Thm_TwoTreeClosure_fst_follow_le
-- name    : TwoTreeClosure.fst_follow_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:26.560358+00:00
-- url     : https://prove2.me/theorems/90065b68-ca6d-4632-988d-716abee9f8d2
-- title:
--   A word of length `L` reaches at most `3 ^ L` times the leading coordinate.
-- statement:
--   A word of length `L` reaches at most `3 ^ L` times the leading coordinate.
--
--   ```lean
--   theorem TwoTreeClosure.fst_follow_le{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
--       ∀ w : List Letter, (follow w v).1 ≤ v.1 * 3 ^ w.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/AscentWord.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/AscentWord.lean#L167

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













/-! ### Depth versus magnitude: the tree is extremely unbalanced

Each branch multiplies the leading coordinate by at most `3`, so a word of length
`L` cannot reach beyond `3 ^ L`.  In the opposite direction the pure `A`-spine
increases the leading coordinate by exactly one per letter, so its depth grows like
the square root of the hypotenuse — the depth of a node is *not* logarithmic in `N`
in general.
-/

theorem TwoTreeClosure.fst_follow_le{v : ℕ × ℕ} (h : IsNode v.1 v.2) :
    ∀ w : List Letter, (follow w v).1 ≤ v.1 * 3 ^ w.length := by sorry
