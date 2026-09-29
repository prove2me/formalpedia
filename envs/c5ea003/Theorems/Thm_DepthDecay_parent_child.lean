-- Prove2me | Theorems.Thm_DepthDecay_parent_child
-- name    : DepthDecay.parent_child
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:30.987374+00:00
-- url     : https://prove2.me/theorems/3545fbfe-085e-43fa-b276-aaf7230b28a2
-- title:
--   The descent undoes each child.
-- statement:
--   The descent undoes each child.
--
--   ```lean
--   theorem DepthDecay.parent_child{s : ℕ × ℕ} (h : Adm s) (x : Letter) :
--       parent (DepthDecay.child x s) = s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/PathRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/PathRealization.lean#L102

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

theorem DepthDecay.parent_child{s : ℕ × ℕ} (h : Adm s) (x : Letter) :
    parent (DepthDecay.child x s) = s := by sorry
