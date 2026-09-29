-- Prove2me | solution 1 for EnergyAscent.balanced_implies_hit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:14:18.918903+00:00
-- url     : https://prove2.me/submissions/cd818bd5-1c7d-4818-a82b-780bdadbdabb

-- Sol generated from Combinatorics/EnergyAscentFermatWindow.lean
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


/-- AM–GM: the Fermat crossing lies to the right of `√N`. -/
theorem sqrt_le_mid {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p * q) ≤ (p + q) / 2 := by
  have h1 : p * q ≤ ((p + q) / 2) ^ 2 := by nlinarith [sq_nonneg (p - q)]
  calc Real.sqrt (p * q) ≤ Real.sqrt (((p + q) / 2) ^ 2) := Real.sqrt_le_sqrt h1
    _ = (p + q) / 2 := Real.sqrt_sq (by linarith)

theorem fermatOffset_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ fermatOffset p q := by
  have := sqrt_le_mid hp hq
  unfold fermatOffset; linarith

/-- The defining identity `(s − √N)(s + √N) = ((q−p)/2)²`. -/
theorem fermatOffset_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    fermatOffset p q * ((p + q) / 2 + Real.sqrt (p * q)) = ((q - p) / 2) ^ 2 := by
  have hr : Real.sqrt (p * q) ^ 2 = p * q := Real.sq_sqrt (by positivity)
  unfold fermatOffset
  nlinarith [hr]


/-- Upper bound: the crossing is at most `(q−p)²/(8√N)` to the right of `√N`. -/
theorem fermatOffset_upper {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    fermatOffset p q ≤ (q - p) ^ 2 / (8 * Real.sqrt (p * q)) := by
  have hrpos : 0 < Real.sqrt (p * q) := Real.sqrt_pos.mpr (by positivity)
  have hnn := fermatOffset_nonneg hp.le hq.le
  have hle := sqrt_le_mid hp.le hq.le
  have hid := fermatOffset_mul hp.le hq.le
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hnn, hle, hid]







/-! ## Sharpness of the scale constant `112` -/




open EnergyAscent in
theorem solution{p q W : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : (q - p) ^ 2 ≤ 8 * W * Real.sqrt (p * q)) : fermatOffset p q ≤ W := by
  have hrpos : 0 < Real.sqrt (p * q) := Real.sqrt_pos.mpr (by positivity)
  have hup := fermatOffset_upper hp hq
  have : (q - p) ^ 2 / (8 * Real.sqrt (p * q)) ≤ W := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h]
  linarith
