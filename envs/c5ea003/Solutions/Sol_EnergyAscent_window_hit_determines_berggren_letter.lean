-- Prove2me | solution 1 for EnergyAscent.window_hit_determines_berggren_letter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:25:12.340341+00:00
-- url     : https://prove2.me/submissions/4a8cfe97-3d50-456f-a12e-521adad643b1

-- Sol generated from Combinatorics/EnergyAscentFermatWindow.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Theorems.Thm_EnergyAscent_branchLetter_eq_one_iff
import Theorems.Thm_EnergyAscent_branch_two_iff
import Theorems.Thm_EnergyAscent_hit_implies_middle_band
import Theorems.Thm_EnergyAscent_no_boundary

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
theorem solution{a b c W : ℤ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hpt : IsPT a b c)
    (hprim : Int.gcd a b = 1) (hW : 0 < W) (hscale : 112 * W ≤ b)
    (hhit : fermatOffset (a : ℝ) (b : ℝ) ≤ (W : ℝ)) :
    branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbc : b < c := by unfold IsPT at hpt; nlinarith
  have hc5 : 5 < c := by omega
  obtain ⟨hne1, hne2⟩ := no_boundary ha hb hc hpt hc5 hprim
  obtain ⟨h1, h2⟩ := hit_implies_middle_band ha hab hscale hhit
  exact ⟨(branchLetter_eq_one_iff a b).mpr ⟨h1, h2⟩,
    (branch_two_iff ha hb hc hpt).mpr ⟨by omega, by omega⟩⟩
