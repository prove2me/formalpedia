-- Prove2me | solution 1 for TwoTreeClosure.exhaustive_beats_guided_of_lt_third
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:17.316733+00:00
-- url     : https://prove2.me/submissions/35b44e90-4351-417e-a0a2-3f295a12588c

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





/-! ### Counting nodes at a fixed depth -/









/-! ### The blind-search adversary bound -/





/-! ### The cost threshold: accuracy `1/3` -/






open TwoTreeClosure in
theorem solution{a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 3) :
    ∃ H : ℕ, ∀ h ≥ H, (3 : ℝ) ^ h < restartEnergy h a := by
  have h3a0 : (0 : ℝ) ≤ 3 * a := by linarith
  have h3a : 3 * a < 1 := by linarith
  have hlim : Tendsto (fun n : ℕ => (3 * a) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h3a0 h3a
  obtain ⟨H, hH⟩ :=
    eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨max H 1, fun h hh => ?_⟩
  have hh1 : 1 ≤ h := le_trans (le_max_right H 1) hh
  have hhH : H ≤ h := le_trans (le_max_left H 1) hh
  have hkey : (3 * a) ^ h < 1 := hH h hhH
  have hah : (0 : ℝ) < a ^ h := pow_pos ha0 h
  have hone : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  rw [restartEnergy, lt_div_iff₀ hah]
  calc (3 : ℝ) ^ h * a ^ h = (3 * a) ^ h := by rw [mul_pow]
    _ < 1 := hkey
    _ ≤ (h : ℝ) := hone
