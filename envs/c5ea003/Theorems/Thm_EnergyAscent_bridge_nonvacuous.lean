-- Prove2me | Theorems.Thm_EnergyAscent_bridge_nonvacuous
-- name    : EnergyAscent.bridge_nonvacuous
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:16:04.671398+00:00
-- url     : https://prove2.me/theorems/1bee5270-15d2-43b1-a1af-0e7be683c8f3
-- title:
--   The bridge is non-vacuous.
-- statement:
--   **The bridge is non-vacuous.**  At every scale there is a primitive
--   Pythagorean triple whose leg pair is a `W = 1` Fermat-window hit above the
--   threshold scale `112`, and for which the magnitude channel of
--   `window_hit_determines_berggren_letter` therefore reads off the branch letter
--   `1` — the middle Berggren generator — correctly.
--
--   ```lean
--   theorem EnergyAscent.bridge_nonvacuous(S : ℤ) :
--       ∃ a b c : ℤ, S < b ∧ 112 ≤ b ∧ 0 < a ∧ a ≤ b ∧ 0 < c ∧ IsPT a b c ∧
--         Int.gcd a b = 1 ∧ fermatOffset (a : ℝ) (b : ℝ) ≤ (1 : ℝ) ∧
--         branchLetter a b = 1 ∧
--         (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentPellSpine.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentPellSpine.lean#L114

-- Thm stub generated from Combinatorics/EnergyAscentPellSpine.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
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

theorem EnergyAscent.bridge_nonvacuous(S : ℤ) :
    ∃ a b c : ℤ, S < b ∧ 112 ≤ b ∧ 0 < a ∧ a ≤ b ∧ 0 < c ∧ IsPT a b c ∧
      Int.gcd a b = 1 ∧ fermatOffset (a : ℝ) (b : ℝ) ≤ (1 : ℝ) ∧
      branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by sorry
