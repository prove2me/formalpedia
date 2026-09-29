-- Prove2me | solution 1 for DepthDecay.letterOf_child
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:24:33.193878+00:00
-- url     : https://prove2.me/submissions/97d2733e-e753-4461-b6b6-d36c9b6f8e4e

-- Sol generated from Cryptography/DepthDecay/PathRealization.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_PathRealization
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# Realizing paths, and an entropy form of the depth decay

The first two files study the descent map `parent` and what a fixed-precision
magnitude probe can read off it.  Here we go the other way: we *build* states
from words, prove that the descent reads the word back letter by letter, and use
that to obtain a counting (pigeonhole) form of the depth decay which is
independent of the explicit straddling construction of
`Cryptography.DepthDecay.NullBeyondInversion`.

## Main results

* `Adm.child`, `letterOf_child`, `parent_child` : the three Berggren children are
  admissibility-preserving sections of the descent, and each child is tagged by
  its own letter.
* `letterAt_build` : the descent path of `build w` is the word `w`.  Every word
  is realized, so the tree really carries `3^k` distinct depth-`k` behaviours.
* `probe_mem_Ico` : on the stratum of states built from `{A,B}`-words the ratio
  stays in `(1,3)`, so a `W`-window probe takes at most `2·2^W` distinct values
  there.
* `probe_collision_of_depth` : **entropy form of the depth decay.**  Once
  `2·2^W < 2^k`, i.e. once the depth exceeds the window budget by two bits, the
  `W`-window sensor must confuse two admissible states whose paths differ at some
  depth below `k`.  The magnitude channel simply does not have the capacity to
  carry the deep letters.
-/

open DepthDecay









/-! ### The bounded-ratio stratum -/







/-! ### Entropy form of the depth decay -/



open DepthDecay in
theorem solution{s : ℕ × ℕ} (h : Adm s) (x : Letter) :
    letterOf (DepthDecay.child x s) = x := by
  obtain ⟨hp, hlt, _, _⟩ := h
  cases x with
  | A => simp [letterOf, DepthDecay.child]; omega
  | B =>
    have h1 : ¬ (2 * s.1 + s.2 < 2 * s.1) := by omega
    have h2 : 2 * s.1 + s.2 < 3 * s.1 := by omega
    simp [letterOf, DepthDecay.child, h1, h2]
  | C =>
    have h1 : ¬ (s.1 + 2 * s.2 < 2 * s.2) := by omega
    have h2 : ¬ (s.1 + 2 * s.2 < 3 * s.2) := by omega
    simp [letterOf, DepthDecay.child, h1, h2]
