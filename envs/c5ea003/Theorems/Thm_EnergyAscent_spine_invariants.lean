-- Prove2me | Theorems.Thm_EnergyAscent_spine_invariants
-- name    : EnergyAscent.spine_invariants
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:15:34.805764+00:00
-- url     : https://prove2.me/theorems/4855aaaa-8f4a-479d-8159-453116c85a2e
-- title:
--   The structural invariants of the spine, proved by a single induction:
-- statement:
--   The structural invariants of the spine, proved by a single induction:
--   positivity, the Pythagorean relation, unit leg gap, and linear growth of the
--   hypotenuse.
--
--   ```lean
--   theorem EnergyAscent.spine_invariants(n : ℕ) :
--       0 < (spine n).1 ∧ 0 < (spine n).2.1 ∧ 0 < (spine n).2.2 ∧
--         IsPT (spine n).1 (spine n).2.1 (spine n).2.2 ∧
--         ((spine n).1 - (spine n).2.1) ^ 2 = 1 ∧
--         (n : ℤ) + 5 ≤ (spine n).2.2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentPellSpine.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentPellSpine.lean#L42

-- Thm stub generated from Combinatorics/EnergyAscentPellSpine.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine

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

open EnergyAscent

theorem EnergyAscent.spine_invariants(n : ℕ) :
    0 < (spine n).1 ∧ 0 < (spine n).2.1 ∧ 0 < (spine n).2.2 ∧
      IsPT (spine n).1 (spine n).2.1 (spine n).2.2 ∧
      ((spine n).1 - (spine n).2.1) ^ 2 = 1 ∧
      (n : ℤ) + 5 ≤ (spine n).2.2 := by sorry
