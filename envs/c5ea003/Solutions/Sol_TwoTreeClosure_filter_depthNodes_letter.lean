-- Prove2me | solution 1 for TwoTreeClosure.filter_depthNodes_letter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:44:09.659756+00:00
-- url     : https://prove2.me/submissions/7d27bf96-3850-45f6-ab23-3f46643c633a

-- Sol generated from Bridges/TwoTreeClosure/SearchLowerBound.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentEconomics
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_SearchLowerBound
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore
import Theorems.Thm_TwoTreeClosure_follow_append
import Theorems.Thm_TwoTreeClosure_follow_isNode
import Theorems.Thm_TwoTreeClosure_letterOf_childOf
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

/-- The root of the Berggren/Price tree is an arithmetic node. -/
theorem isNode_root : IsNode 2 1 := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
  simp [Nat.Coprime]

/-! ### Counting words -/





/-! ### Counting nodes at a fixed depth -/



theorem mem_depthNodes {h : ℕ} {p : ℕ × ℕ} :
    p ∈ depthNodes h ↔ ∃ w : List Letter, w.length = h ∧ follow w (2, 1) = p := by
  simp only [depthNodes, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_words_iff h w).mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_words_iff h w).mpr hw, rfl⟩


/-- The last letter of a word is the ascent letter of the node it reaches. -/
theorem letterOf_follow_concat (u : List Letter) (l : Letter) :
    letterOf (follow (u ++ [l]) (2, 1)).1 (follow (u ++ [l]) (2, 1)).2 = l := by
  rw [follow_append]
  exact letterOf_childOf l (follow_isNode isNode_root u)




/-! ### The blind-search adversary bound -/





/-! ### The cost threshold: accuracy `1/3` -/






open TwoTreeClosure in
theorem solution(h : ℕ) (l : Letter) :
    (depthNodes (h + 1)).filter (fun p => letterOf p.1 p.2 = l)
      = (words h).image (fun w => follow (w ++ [l]) (2, 1)) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image, mem_depthNodes]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hl⟩
    rcases List.eq_nil_or_concat w with rfl | ⟨u, l', rfl⟩
    · simp at hw
    · rw [List.concat_eq_append] at hw hl ⊢
      have hu : u.length = h := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have : l' = l := by rw [← letterOf_follow_concat u l']; exact hl
      subst this
      exact ⟨u, (mem_words_iff h u).mpr hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hu' : u.length = h := (mem_words_iff h u).mp hu
    refine ⟨⟨u ++ [l], by simp [hu'], rfl⟩, letterOf_follow_concat u l⟩
