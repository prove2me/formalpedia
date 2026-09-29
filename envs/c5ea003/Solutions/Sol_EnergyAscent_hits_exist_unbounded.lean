-- Prove2me | solution 1 for EnergyAscent.hits_exist_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:02.625987+00:00
-- url     : https://prove2.me/submissions/67d84b42-c403-4927-97f4-53decd4c94be

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
theorem solution(W : ℤ) (hW : 0 < W) (S : ℤ) :
    ∃ p q : ℤ, S < p ∧ p < q ∧ 112 * W ≤ q ∧
      fermatOffset (p : ℝ) (q : ℝ) ≤ (W : ℝ) := by
  set p : ℤ := max (S + 1) (112 * W) with hpdef
  have hpS : S < p := lt_of_lt_of_le (lt_add_one S) (le_max_left _ _)
  have hpW : 112 * W ≤ p := le_max_right _ _
  have hp1 : (1 : ℤ) ≤ p := by omega
  refine ⟨p, p + 1, hpS, by omega, by omega, ?_⟩
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hWR : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hsq : (1 : ℝ) ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) + 1)) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (p : ℝ) * ((p : ℝ) + 1) by nlinarith)
    rwa [Real.sqrt_one] at h
  have hcast : ((p + 1 : ℤ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  refine balanced_implies_hit (by linarith) (by linarith) ?_
  have hone : ((p : ℝ) + 1 - p) ^ 2 = 1 := by ring
  rw [hone]
  nlinarith [hsq, hWR]
