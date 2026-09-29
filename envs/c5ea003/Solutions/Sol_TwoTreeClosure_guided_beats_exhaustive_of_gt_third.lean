-- Prove2me | solution 1 for TwoTreeClosure.guided_beats_exhaustive_of_gt_third
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:47:37.665061+00:00
-- url     : https://prove2.me/submissions/e62139ac-e6d3-454e-a1a0-1e5a1e9b7be4

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
theorem solution{a : ℝ} (ha : 1 / 3 < a) :
    ∃ H : ℕ, ∀ h ≥ H, restartEnergy h a < 3 ^ h := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have h3a : (1 : ℝ) < 3 * a := by linarith
  set r : ℝ := (3 * a)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, inv_lt_one₀ (by linarith)]
    exact h3a
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  obtain ⟨H, hH⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨H, fun h hh => ?_⟩
  have hkey : (h : ℝ) * r ^ h < 1 := hH h hh
  have hpow : (0 : ℝ) < (3 * a) ^ h := pow_pos (by linarith) h
  have hrh : r ^ h = ((3 * a) ^ h)⁻¹ := by
    rw [hr, ← inv_pow]
  rw [hrh, ← div_eq_mul_inv, div_lt_one hpow] at hkey
  have hah : (0 : ℝ) < a ^ h := pow_pos ha0 h
  rw [restartEnergy, div_lt_iff₀ hah]
  calc (h : ℝ) < (3 * a) ^ h := hkey
    _ = 3 ^ h * a ^ h := by rw [mul_pow]
