-- Prove2me | Theorems.Thm_EnergyAscent_balanced_implies_hit
-- name    : EnergyAscent.balanced_implies_hit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:14:15.505835+00:00
-- url     : https://prove2.me/theorems/6ff24ada-a653-41be-b889-5bfa14ab2c95
-- title:
--   A sufficient condition for a window hit.
-- statement:
--   A sufficient condition for a window hit.
--
--   ```lean
--   theorem EnergyAscent.balanced_implies_hit{p q W : ℝ} (hp : 0 < p) (hq : 0 < q)
--       (h : (q - p) ^ 2 ≤ 8 * W * Real.sqrt (p * q)) : fermatOffset p q ≤ W := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentFermatWindow.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentFermatWindow.lean#L137

-- Thm stub generated from Combinatorics/EnergyAscentFermatWindow.lean
import Mathlib
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

theorem EnergyAscent.balanced_implies_hit{p q W : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : (q - p) ^ 2 ≤ 8 * W * Real.sqrt (p * q)) : fermatOffset p q ≤ W := by sorry
