-- Prove2me | solution 1 for EnergyAscent.hit_implies_middle_band
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:23:40.413972+00:00
-- url     : https://prove2.me/submissions/28ecbf13-dcd9-41a6-8279-42b639d35522

-- Sol generated from Combinatorics/EnergyAscentFermatWindow.lean
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Theorems.Thm_EnergyAscent_window_hit_ratio_bound

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













/-! ## Sharpness of the scale constant `112` -/




open EnergyAscent in
theorem solution{p q W : ℤ} (hp : 0 < p) (hpq : p ≤ q)
    (hscale : 112 * W ≤ q) (hhit : fermatOffset (p : ℝ) (q : ℝ) ≤ (W : ℝ)) :
    3 * q ≤ 4 * p ∧ 3 * p ≤ 4 * q := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hR : ((q : ℝ) - p) ^ 2 ≤ 4 * (W : ℝ) * ((p : ℝ) + q) :=
    window_hit_ratio_bound (by exact_mod_cast hp) (by exact_mod_cast hq) hhit
  have hZ : (q - p) ^ 2 ≤ 4 * W * (p + q) := by exact_mod_cast hR
  refine ⟨?_, by omega⟩
  by_contra hcon
  push_neg at hcon
  -- `4p < 3q` gives `4(q−p) > q` and `4(p+q) ≤ 7q`, whence `q < 112 W`.
  have h1 : q < 4 * (q - p) := by omega
  have h2 : 4 * (p + q) ≤ 7 * q := by omega
  have hqp : 0 < q - p := by omega
  nlinarith [hZ, h1, h2, hqp, hscale]
