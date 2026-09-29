-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_SearchLowerBound
-- name    : Bridges_TwoTreeClosure_SearchLowerBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:51.897774+00:00
-- url     : https://prove2.me/theorems/1fea6f66-df68-42e0-9cb5-6e97fe851512
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_SearchLowerBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.SearchLowerBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/SearchLowerBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentEconomics
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# Search lower bounds and exact letter counts on the Berggren/Price tree

Third cycle of the two-tree programme.  `TreeCore` shows that no cheap probe reads
the ascent letter from `N`; `AscentWord` shows that the letters *are* a normal form.
This file quantifies what a searcher who cannot read the letters must pay, and how
much letter information the tree measure itself carries.

* `words h` enumerates the `{A,B,C}`-words of length `h`; `card_words` : there are
  exactly `3 ^ h` of them and `mem_words_iff` characterises membership by length.
* `depthNodes h` is the set of nodes at depth `h` below the root; `card_depthNodes`
  gives it exactly `3 ^ h` elements (an ascent-word refinement of `card_desc`).
* `card_depthNodes_letter` : **exact letter equidistribution over the tree measure** —
  for every letter `L`, exactly `3 ^ h` of the `3 ^ (h+1)` nodes at depth `h + 1`
  carry the letter `L`.  So a *uniform* node at depth `h+1` carries a full
  `log₂ 3` bits of last-letter entropy, while the blindness theorems of `TreeCore`
  say that none of it is readable from the hypotenuse.
* `exists_unvisited_node`, `majority_unvisited` : the adversary/pigeonhole lower
  bound.  A blind searcher who visits fewer than `3 ^ h` nodes misses some depth-`h`
  node, and one who visits fewer than `3 ^ h / 2` misses a strict majority of them.
* `restart_beats_exhaustive_half`, `guided_beats_exhaustive_of_gt_third`,
  `exhaustive_beats_guided_of_lt_third` : the accuracy threshold at which the
  restarted guided ascent overtakes exhaustive search is exactly `1/3` — the
  reciprocal of the branching base pinned by `card_desc`.  This is the *cost* side of
  the closure, complementing the *budget* side `0.85 < α* ≤ 0.86` of
  `AscentEconomics`.
-/

namespace TwoTreeClosure

open Finset Filter


/-! ### Counting words -/

/-- All `{A,B,C}`-words of a given length, built by appending a final letter. -/
def words : ℕ → Finset (List Letter)
  | 0 => {[]}
  | h + 1 =>
      (words h).image (fun w => w ++ [Letter.A]) ∪
        ((words h).image (fun w => w ++ [Letter.B]) ∪
          (words h).image (fun w => w ++ [Letter.C]))




/-! ### Counting nodes at a fixed depth -/

/-- The nodes at depth `h` below the root, indexed by their ascent words. -/
def depthNodes (h : ℕ) : Finset (ℕ × ℕ) := (words h).image (fun w => follow w (2, 1))








/-! ### The blind-search adversary bound -/





/-! ### The cost threshold: accuracy `1/3` -/





end TwoTreeClosure


