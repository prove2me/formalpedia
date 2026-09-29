-- Prove2me | Definitions.Def_Cryptography_DepthDecay_PathRealization
-- name    : Cryptography_DepthDecay_PathRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:00.232626+00:00
-- url     : https://prove2.me/theorems/0bf7a0ab-c644-42eb-9769-08a0f3bf8ecf
-- title:
--   Aether Catalog definitions — Cryptography_DepthDecay_PathRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.DepthDecay.PathRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/DepthDecay/PathRealization.lean by skeleton subtraction
import Mathlib
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

namespace DepthDecay

/-- The three Berggren children in `(m,n)` coordinates. -/
def child : Letter → ℕ × ℕ → ℕ × ℕ
  | Letter.A, s => (2 * s.1 - s.2, s.1)
  | Letter.B, s => (2 * s.1 + s.2, s.1)
  | Letter.C, s => (s.1 + 2 * s.2, s.2)

/-- The state built from a word, the head of the word being the last child taken
(hence the first letter of the descent). -/
def build : List Letter → ℕ × ℕ
  | [] => root
  | x :: w => child x (build w)







/-! ### The bounded-ratio stratum -/



/-- The `{A,B}`-word attached to a Boolean vector. -/
def boolWord {k : ℕ} (v : Fin k → Bool) : List Letter :=
  List.ofFn (fun i : Fin k => if v i then Letter.A else Letter.B)




/-! ### Entropy form of the depth decay -/


end DepthDecay


