-- Prove2me | Theorems.Thm_EnergyAscent_spine_sorted
-- name    : EnergyAscent.spine_sorted
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:15:45.045704+00:00
-- url     : https://prove2.me/theorems/64d8e935-5b74-4dbe-b8bf-6f5bf34d5563
-- title:
--   Every spine member, written with its legs in increasing order, is a
-- statement:
--   Every spine member, written with its legs in increasing order, is a
--   primitive Pythagorean triple whose legs are consecutive integers.
--
--   ```lean
--   theorem EnergyAscent.spine_sorted(n : ℕ) :
--       ∃ p c : ℤ, 0 < p ∧ 0 < c ∧ IsPT p (p + 1) c ∧ Int.gcd p (p + 1) = 1 ∧
--         (n : ℤ) + 5 ≤ c ∧ c < p + (p + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentPellSpine.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentPellSpine.lean#L87

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

theorem EnergyAscent.spine_sorted(n : ℕ) :
    ∃ p c : ℤ, 0 < p ∧ 0 < c ∧ IsPT p (p + 1) c ∧ Int.gcd p (p + 1) = 1 ∧
      (n : ℤ) + 5 ≤ c ∧ c < p + (p + 1) := by sorry
