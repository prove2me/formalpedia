-- Prove2me | solution 1 for EnergyAscent.hit_of_quartic_criterion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:01.942987+00:00
-- url     : https://prove2.me/submissions/f6997638-a2eb-4d6f-98db-1a09d9bc00da

-- Sol generated from Combinatorics/EnergyAscentFermatWindow.lean
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Theorems.Thm_EnergyAscent_balanced_implies_hit

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
theorem solution{p q W : ℤ} (hp : 0 < p) (hq : 0 < q) (hW : 0 < W)
    (h : (q - p) ^ 4 ≤ 64 * W ^ 2 * (p * q)) :
    fermatOffset (p : ℝ) (q : ℝ) ≤ (W : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hR : ((q : ℝ) - p) ^ 4 ≤ 64 * (W : ℝ) ^ 2 * ((p : ℝ) * q) := by exact_mod_cast h
  have hs : (0 : ℝ) ≤ Real.sqrt ((p : ℝ) * q) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((p : ℝ) * q) ^ 2 = (p : ℝ) * q := Real.sq_sqrt (by positivity)
  refine balanced_implies_hit hpR hqR ?_
  by_contra hcon
  push_neg at hcon
  have hA : (0 : ℝ) ≤ 8 * (W : ℝ) * Real.sqrt ((p : ℝ) * q) := by positivity
  have h2 := mul_self_lt_mul_self hA hcon
  nlinarith [h2, hsq, hR]
