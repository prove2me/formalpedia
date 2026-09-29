-- Prove2me | Definitions.Def_Combinatorics_EnergyAscentPellSpine
-- name    : Combinatorics_EnergyAscentPellSpine
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:41:18.3161+00:00
-- url     : https://prove2.me/theorems/49d7ecce-cc9b-4308-9243-0bee45a97cf4
-- title:
--   Aether Catalog definitions — Combinatorics_EnergyAscentPellSpine
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EnergyAscentPellSpine`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EnergyAscentPellSpine.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow

/-!
# Energy-Ascent IV: the `B₂`-spine realises the window channel

The bridge theorem `EnergyAscent.window_hit_determines_berggren_letter` says
that a Fermat-window hit on the legs of a primitive Pythagorean triple pins its
Berggren branch letter.  A theorem of that shape is worthless if its hypotheses
are never met, so here we exhibit an explicit infinite family that meets them:
the **`B₂`-spine** of the Berggren tree, obtained by iterating the middle
generator from the root `(3, 4, 5)`.

Its members `(3,4,5), (21,20,29), (119,120,169), (697,696,985), …` have legs
differing by exactly `1`; hence they are automatically primitive, they are
window hits for the *smallest possible* window `W = 1`, and their hypotenuses
grow geometrically.  So the magnitude channel of Energy-Ascent III fires
infinitely often, and every time it fires it reads the letter correctly.

## Main results

* `EnergyAscent.spine_invariants`: the spine consists of primitive Pythagorean
  triples with `(a − b)² = 1` and geometric growth.
* `EnergyAscent.spine_is_window_hit`: every spine member is a `W = 1` window hit.
* `EnergyAscent.bridge_nonvacuous`: at every scale there is a primitive
  Pythagorean triple to which the bridge theorem applies, and whose branch
  letter it correctly determines to be `1`.
-/

namespace EnergyAscent

/-- The `B₂`-spine of the Berggren tree: iterate the middle Barning–Hall
generator starting from the root `(3, 4, 5)`. -/
def spine : ℕ → ℤ × ℤ × ℤ
  | 0 => (3, 4, 5)
  | n + 1 => B2 (spine n).1 (spine n).2.1 (spine n).2.2









end EnergyAscent


