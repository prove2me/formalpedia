-- Prove2me | solution 1 for EnergyAscent.bridge_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:27:03.811245+00:00
-- url     : https://prove2.me/submissions/816b8db4-1b56-4ddc-8dc9-75934df08394

-- Sol generated from Combinatorics/EnergyAscentPellSpine.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
import Theorems.Thm_EnergyAscent_balanced_implies_hit
import Theorems.Thm_EnergyAscent_spine_sorted
import Theorems.Thm_EnergyAscent_window_hit_determines_berggren_letter

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







/-- A factor pair with unit gap is a window hit for the smallest window `W = 1`. -/
theorem unit_gap_hit {p : ℤ} (hp : 0 < p) :
    fermatOffset (p : ℝ) ((p : ℝ) + 1) ≤ (1 : ℝ) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : (1 : ℝ) ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) + 1)) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (p : ℝ) * ((p : ℝ) + 1) by nlinarith)
    rwa [Real.sqrt_one] at h
  refine balanced_implies_hit (by linarith) (by linarith) ?_
  have hone : ((p : ℝ) + 1 - p) ^ 2 = 1 := by ring
  rw [hone]
  nlinarith [hsq]




open EnergyAscent in
theorem solution(S : ℤ) :
    ∃ a b c : ℤ, S < b ∧ 112 ≤ b ∧ 0 < a ∧ a ≤ b ∧ 0 < c ∧ IsPT a b c ∧
      Int.gcd a b = 1 ∧ fermatOffset (a : ℝ) (b : ℝ) ≤ (1 : ℝ) ∧
      branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max (2 * S) 224 ≤ (n : ℤ) := ⟨(max (2 * S) 224).toNat, by omega⟩
  obtain ⟨p, c, hp, hc, hpt, hcop, hgrow, hsum⟩ := spine_sorted n
  have hS : 2 * S ≤ (n : ℤ) := le_trans (le_max_left _ _) hn
  have h224 : (224 : ℤ) ≤ (n : ℤ) := le_trans (le_max_right _ _) hn
  have hpbig : 112 ≤ p := by omega
  have hhit : fermatOffset (p : ℝ) ((p : ℝ) + 1) ≤ (1 : ℝ) := unit_gap_hit hp
  have hcast : ((p + 1 : ℤ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  obtain ⟨hletter, hparent⟩ :=
    window_hit_determines_berggren_letter (a := p) (b := p + 1) (c := c) (W := 1)
      hp (by omega) hc hpt hcop (by norm_num) (by omega) (by rw [hcast]; simpa using hhit)
  exact ⟨p, p + 1, c, by omega, by omega, hp, by omega, hc, hpt, hcop,
    by rw [hcast]; simpa using hhit, hletter, hparent⟩
