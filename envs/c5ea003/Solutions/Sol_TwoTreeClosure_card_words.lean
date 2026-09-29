-- Prove2me | solution 1 for TwoTreeClosure.card_words
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:15:11.258513+00:00
-- url     : https://prove2.me/submissions/5236644b-d182-42e9-a799-ecc8f5a1bc0a

-- Sol generated from Bridges/TwoTreeClosure/SearchLowerBound.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_AscentEconomics
import Definitions.Def_Bridges_TwoTreeClosure_AscentWord
import Definitions.Def_Bridges_TwoTreeClosure_SearchLowerBound
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

open TwoTreeClosure

open Finset Filter


/-! ### Counting words -/



theorem append_letter_injective (l : Letter) :
    Function.Injective (fun w : List Letter => w ++ [l]) := by
  intro u v huv
  simpa using huv


/-! ### Counting nodes at a fixed depth -/









/-! ### The blind-search adversary bound -/





/-! ### The cost threshold: accuracy `1/3` -/






open TwoTreeClosure in
theorem solution: ∀ h : ℕ, (words h).card = 3 ^ h := by
  intro h
  induction h with
  | zero => simp [words]
  | succ h ih =>
      have hA : ((words h).image (fun w => w ++ [Letter.A])).card = 3 ^ h := by
        rw [Finset.card_image_of_injective _ (append_letter_injective Letter.A), ih]
      have hB : ((words h).image (fun w => w ++ [Letter.B])).card = 3 ^ h := by
        rw [Finset.card_image_of_injective _ (append_letter_injective Letter.B), ih]
      have hC : ((words h).image (fun w => w ++ [Letter.C])).card = 3 ^ h := by
        rw [Finset.card_image_of_injective _ (append_letter_injective Letter.C), ih]
      have hlast : ∀ (l : Letter) (u : List Letter), (u ++ [l]).getLast? = some l := by
        intro l u
        simp
      have hdisj : ∀ l l' : Letter, l ≠ l' →
          Disjoint ((words h).image (fun w => w ++ [l]))
            ((words h).image (fun w => w ++ [l'])) := by
        intro l l' hll
        rw [Finset.disjoint_left]
        rintro a ha ha'
        simp only [Finset.mem_image] at ha ha'
        obtain ⟨u, -, rfl⟩ := ha
        obtain ⟨v, -, hv⟩ := ha'
        have := hlast l u
        rw [← hv, hlast l' v] at this
        exact hll (Option.some_injective _ this).symm
      have hBC : Disjoint ((words h).image (fun w => w ++ [Letter.B]))
          ((words h).image (fun w => w ++ [Letter.C])) := hdisj _ _ (by decide)
      have hAB : Disjoint ((words h).image (fun w => w ++ [Letter.A]))
          ((words h).image (fun w => w ++ [Letter.B]) ∪
            (words h).image (fun w => w ++ [Letter.C])) := by
        rw [Finset.disjoint_union_right]
        exact ⟨hdisj _ _ (by decide), hdisj _ _ (by decide)⟩
      simp only [words]
      rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC, hA, hB, hC]
      ring
