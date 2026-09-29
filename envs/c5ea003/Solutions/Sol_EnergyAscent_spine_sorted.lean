-- Prove2me | solution 1 for EnergyAscent.spine_sorted
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:22:15.016296+00:00
-- url     : https://prove2.me/submissions/d1ab13d8-4149-4b08-bf6d-59c932580408

-- Sol generated from Combinatorics/EnergyAscentPellSpine.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
import Theorems.Thm_EnergyAscent_hyp_lt_sum
import Theorems.Thm_EnergyAscent_spine_invariants

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











open EnergyAscent in
theorem solution(n : ℕ) :
    ∃ p c : ℤ, 0 < p ∧ 0 < c ∧ IsPT p (p + 1) c ∧ Int.gcd p (p + 1) = 1 ∧
      (n : ℤ) + 5 ≤ c ∧ c < p + (p + 1) := by
  obtain ⟨ha, hb, hc, hpt, hgap, hgrow⟩ := spine_invariants n
  set a := (spine n).1
  set b := (spine n).2.1
  set c := (spine n).2.2
  have hlt : c < a + b := hyp_lt_sum ha hb hc hpt
  have h1 : a - b ≤ 1 := by nlinarith
  have h2 : -1 ≤ a - b := by nlinarith
  have h3 : a - b ≠ 0 := by
    intro h
    rw [h] at hgap
    norm_num at hgap
  have hcases : a = b + 1 ∨ b = a + 1 := by omega
  have hcop : ∀ x : ℤ, Int.gcd x (x + 1) = 1 := by
    intro x
    exact Int.isCoprime_iff_gcd_eq_one.mp ⟨-1, 1, by ring⟩
  rcases hcases with h | h
  · refine ⟨b, c, hb, hc, ?_, hcop b, hgrow, by omega⟩
    unfold IsPT at hpt ⊢
    rw [← h]
    linarith [hpt]
  · exact ⟨a, c, ha, hc, by rw [← h]; exact hpt, hcop a, hgrow, by omega⟩
