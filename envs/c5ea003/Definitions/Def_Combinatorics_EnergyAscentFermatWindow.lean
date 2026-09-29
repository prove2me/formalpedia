-- Prove2me | Definitions.Def_Combinatorics_EnergyAscentFermatWindow
-- name    : Combinatorics_EnergyAscentFermatWindow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:39:45.599293+00:00
-- url     : https://prove2.me/theorems/9a264178-caf9-4122-bd4d-0e8102df24c3
-- title:
--   Aether Catalog definitions — Combinatorics_EnergyAscentFermatWindow
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EnergyAscentFermatWindow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EnergyAscentFermatWindow.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters

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

namespace EnergyAscent

open Real

/-- The Fermat offset of a factorisation `N = p·q`: the distance from `√N` to
the abscissa `(p+q)/2` where the parabola `x ↦ x² − N` becomes a square. -/
noncomputable def fermatOffset (p q : ℝ) : ℝ := (p + q) / 2 - Real.sqrt (p * q)












/-! ## Sharpness of the scale constant `112` -/



end EnergyAscent


