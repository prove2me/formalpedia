-- Prove2me | Theorems.Thm_EnergyAscent_window_hit_determines_berggren_letter
-- name    : EnergyAscent.window_hit_determines_berggren_letter
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:15:52.501001+00:00
-- url     : https://prove2.me/theorems/34a9e738-0831-486c-b008-d7b57691a033
-- title:
--   Cross-domain bridge.
-- statement:
--   **Cross-domain bridge.**  For a primitive Pythagorean triple whose leg pair
--   lies above scale `112·W`, a Fermat-window hit on the legs determines the
--   Berggren branch letter: it must be the middle letter, and the tree parent is the
--   `invB2` descent.  A magnitude/position channel reads a tree letter.
--
--   ```lean
--   theorem EnergyAscent.window_hit_determines_berggren_letter{a b c W : ℤ}
--       (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hpt : IsPT a b c)
--       (hprim : Int.gcd a b = 1) (hW : 0 < W) (hscale : 112 * W ≤ b)
--       (hhit : fermatOffset (a : ℝ) (b : ℝ) ≤ (W : ℝ)) :
--       branchLetter a b = 1 ∧
--         (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentFermatWindow.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentFermatWindow.lean#L119

-- Thm stub generated from Combinatorics/EnergyAscentFermatWindow.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow

/-!
# Energy-Ascent III: the Fermat window is a positional ratio sensor

This file formalises the *mechanism* half of the ENERGY-ASCENT round.  The
empirical claim was that the magnitude spectrum of the Fermat energy
`E(a) = a² − N` read in a fixed window `W` anchored at `⌊√N⌋` behaves as a
**positional sensor of the parabola zero crossing**, with a hit rate that
depends strongly on the ratio band (measured rates `{0.000, 0.019, 0.673}` by
letter) — and *not* on any residue datum.

We prove the exact deterministic skeleton behind those numbers.

## Main results

* `EnergyAscent.fermatOffset_lower` / `fermatOffset_upper`: two-sided bounds
  `(q−p)²/(4(p+q)) ≤ (p+q)/2 − √(pq) ≤ (q−p)²/(8√(pq))`, i.e. the zero crossing
  of the Fermat parabola sits at distance `≍ (q−p)²/√N` from `√N`.
* `EnergyAscent.fermatOffset_scale`: the offset is homogeneous of degree one,
  so the *relative* offset is a function of the ratio alone — the sensor is
  positional.
* `EnergyAscent.window_hit_ratio_bound`: a window hit forces `(q−p)² ≤ 4W(p+q)`.
* `EnergyAscent.hit_implies_middle_band`: above scale `112·W` a window hit
  **forces the middle ratio band**.  This is the deterministic core of the
  measured hit-rate table: the outer letters have hit rate exactly `0` there.
* `EnergyAscent.window_hit_determines_berggren_letter`: consequently, for a
  primitive Pythagorean triple above that scale, a window hit on its leg pair
  pins the Berggren branch letter to `1` and names `invB2` as its parent — a
  magnitude channel reading a tree letter.
* `EnergyAscent.hits_exist_unbounded`: the channel is not vacuous; hits occur at
  every scale.
-/

open EnergyAscent

open Real

theorem EnergyAscent.window_hit_determines_berggren_letter{a b c W : ℤ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hpt : IsPT a b c)
    (hprim : Int.gcd a b = 1) (hW : 0 < W) (hscale : 112 * W ≤ b)
    (hhit : fermatOffset (a : ℝ) (b : ℝ) ≤ (W : ℝ)) :
    branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by sorry
