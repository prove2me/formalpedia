-- Prove2me | solution 1 for TwoTreeClosure.adaptive_search_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:16:55.846285+00:00
-- url     : https://prove2.me/submissions/5c285e32-7660-4d2d-bc10-eb1d04c63f86

-- Sol generated from Bridges/TwoTreeClosure/SearchLowerBound.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentEconomics
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_SearchLowerBound
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_card_words
import Theorems.Thm_TwoTreeClosure_mem_words_iff

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

open TwoTreeClosure

open Finset Filter


/-! ### Counting words -/





/-! ### Counting nodes at a fixed depth -/









/-! ### The blind-search adversary bound -/





/-! ### The cost threshold: accuracy `1/3` -/






open TwoTreeClosure in
theorem solution(S : ℕ → List Letter) (k h : ℕ) (hk : k < 3 ^ h) :
    ∃ w : List Letter, w.length = h ∧ ∀ i < k, S i ≠ w := by
  by_contra hcon
  push_neg at hcon
  have hsub : words h ⊆ (Finset.range k).image S := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := hcon w ((mem_words_iff h w).mp hw)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hiw⟩
  have h1 : (words h).card ≤ ((Finset.range k).image S).card := Finset.card_le_card hsub
  have h2 : ((Finset.range k).image S).card ≤ k := by
    calc ((Finset.range k).image S).card ≤ (Finset.range k).card := Finset.card_image_le
      _ = k := Finset.card_range k
  rw [card_words] at h1
  omega
