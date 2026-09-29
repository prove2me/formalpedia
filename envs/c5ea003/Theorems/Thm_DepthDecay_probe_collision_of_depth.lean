-- Prove2me | Theorems.Thm_DepthDecay_probe_collision_of_depth
-- name    : DepthDecay.probe_collision_of_depth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:44.082334+00:00
-- url     : https://prove2.me/theorems/edeab530-1477-46b7-988f-dfe1cffa9484
-- title:
--   Capacity bound.
-- statement:
--   **Capacity bound.**  As soon as the depth `k` exceeds the window budget by two
--   bits (`2 · 2^W < 2^k`), the `W`-window magnitude sensor confuses two admissible
--   states whose descent paths already differ at a depth below `k`.  No fixed-budget
--   magnitude functional can transmit `k` letters of the path.
--
--   ```lean
--   theorem DepthDecay.probe_collision_of_depth(W k : ℕ) (hk : 2 * 2 ^ W < 2 ^ k) :
--       ∃ s s' : ℕ × ℕ, Adm s ∧ Adm s' ∧ probe W s = probe W s' ∧
--         ∃ j < k, letterAt j s ≠ letterAt j s' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/PathRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/PathRealization.lean#L186

-- Thm stub generated from Cryptography/DepthDecay/PathRealization.lean
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

theorem DepthDecay.probe_collision_of_depth(W k : ℕ) (hk : 2 * 2 ^ W < 2 ^ k) :
    ∃ s s' : ℕ × ℕ, Adm s ∧ Adm s' ∧ probe W s = probe W s' ∧
      ∃ j < k, letterAt j s ≠ letterAt j s' := by sorry
