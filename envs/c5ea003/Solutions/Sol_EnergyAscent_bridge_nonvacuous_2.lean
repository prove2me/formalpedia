-- Prove2me | solution 2 for EnergyAscent.bridge_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:37.053986+00:00
-- url     : https://prove2.me/submissions/9fe8d844-3476-47b2-9138-97bb4608e02d

-- Thm stub generated from Combinatorics/EnergyAscentPellSpine.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine

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

open scoped Classical
open Real
theorem parent_hyp_lt (a b c : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpt : IsPT a b c) : -2*a - 2*b + 3*c < c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (a + b - c), sq_nonneg (a - b)]

theorem parent_hyp_pos (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 0 < -2*a - 2*b + 3*c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (3*c - 2*a - 2*b), sq_nonneg (a - b), mul_pos ha hb]

theorem not_both_neg (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hpt : IsPT a b c)
    (h3 : a + 2 * b ≤ 2 * c) (h4 : 2 * a + b ≤ 2 * c) : False := by
  unfold IsPT at hpt
  have hc : 0 < c := by nlinarith
  have k1 : 4 * b ≤ 3 * a := by nlinarith
  have k2 : 4 * a ≤ 3 * b := by nlinarith
  nlinarith

theorem invB1_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b > 2 * c) (h4 : 2 * a + b < 2 * c) :
    0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2 := by
  refine ⟨by simp [invB1]; omega, by simp [invB1]; omega, ?_⟩
  simpa [invB1] using parent_hyp_pos a b c ha hb hc hpt

theorem invB2_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b > 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2 := by
  refine ⟨by simp [invB2]; omega, by simp [invB2]; omega, ?_⟩
  simpa [invB2] using parent_hyp_pos a b c ha hb hc hpt

theorem invB3_pos_case (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (h3 : a + 2 * b < 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2 := by
  refine ⟨by simp [invB3]; omega, by simp [invB3]; omega, ?_⟩
  simpa [invB3] using parent_hyp_pos a b c ha hb hc hpt

theorem parent_exists (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
    (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
    (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by
  have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hprim
  by_cases h1 : a + 2 * b = 2 * c
  · -- `a + 2b = 2c` forces `3a = 4b`, hence `(a, b, c) = (4, 3, 5)`, contradicting `c > 5`.
    exfalso
    have heq : 3 * a = 4 * b := by unfold IsPT at hpt; nlinarith
    have hda : a ∣ 4 := hcop.dvd_of_dvd_mul_right ⟨3, by linarith⟩
    have hdb : b ∣ 3 := hcop.symm.dvd_of_dvd_mul_right ⟨4, by linarith⟩
    have ha4 : a ≤ 4 := Int.le_of_dvd (by norm_num) hda
    have hb3 : b ≤ 3 := Int.le_of_dvd (by norm_num) hdb
    omega
  · by_cases h2 : 2 * a + b = 2 * c
    · -- symmetrically, `2a + b = 2c` forces `(a, b, c) = (3, 4, 5)`.
      exfalso
      have heq : 3 * b = 4 * a := by unfold IsPT at hpt; nlinarith
      have hdb : b ∣ 4 := hcop.symm.dvd_of_dvd_mul_right ⟨3, by linarith⟩
      have hda : a ∣ 3 := hcop.dvd_of_dvd_mul_right ⟨4, by linarith⟩
      have hb4 : b ≤ 4 := Int.le_of_dvd (by norm_num) hdb
      have ha3 : a ≤ 3 := Int.le_of_dvd (by norm_num) hda
      omega
    · by_cases h3 : a + 2 * b > 2 * c <;> by_cases h4 : 2 * a + b > 2 * c
      · exact Or.inr <| Or.inl <| invB2_pos_case a b c ha hb hc hpt h3 h4
      · exact Or.inl <| invB1_pos_case a b c ha hb hc hpt h3
          (lt_of_le_of_ne (le_of_not_gt h4) h2)
      · exact Or.inr <| Or.inr <| invB3_pos_case a b c ha hb hc hpt
          (lt_of_le_of_ne (le_of_not_gt h3) h1) h4
      · exact False.elim <| not_both_neg a b c ha hb hpt (le_of_not_gt h3) (le_of_not_gt h4)

namespace EnergyAscent

theorem leg_lt_hyp {a b c : ℤ} (hb : 0 < b) (hc : 0 < c) (hpt : IsPT a b c) : a < c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]

end EnergyAscent

namespace EnergyAscent

theorem hyp_lt_sum {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : c < a + b := by
  unfold IsPT at hpt
  nlinarith [mul_pos ha hb]

end EnergyAscent

namespace EnergyAscent

theorem cond_left_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c < a + 2 * b ↔ 3 * a < 4 * b := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c), sq_nonneg (a + 2 * b + 2 * c)]

end EnergyAscent

namespace EnergyAscent

theorem cond_right_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c < 2 * a + b ↔ 3 * b < 4 * a := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c), sq_nonneg (2 * a + b + 2 * c)]

end EnergyAscent

namespace EnergyAscent

theorem cond_left_le_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c ≤ a + 2 * b ↔ 3 * a ≤ 4 * b := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (a + 2 * b - 2 * c), sq_nonneg (a + 2 * b + 2 * c)]

end EnergyAscent

namespace EnergyAscent

theorem cond_right_le_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 2 * c ≤ 2 * a + b ↔ 3 * b ≤ 4 * a := by
  unfold IsPT at hpt
  constructor
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c)]
  · intro h
    nlinarith [sq_nonneg (2 * a + b - 2 * c), sq_nonneg (2 * a + b + 2 * c)]

end EnergyAscent

namespace EnergyAscent

theorem branch_one_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) :
    (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ↔
      4 * a < 3 * b := by
  have hL := EnergyAscent.cond_left_iff ha hb hc hpt
  have hRle := EnergyAscent.cond_right_le_iff ha hb hc hpt
  have hpos := parent_hyp_pos a b c ha hb hc hpt
  constructor
  · rintro ⟨-, h2, -⟩
    simp only [invB1] at h2
    have hnot : ¬ (3 * b ≤ 4 * a) := fun hcon => by have := hRle.mpr hcon; omega
    omega
  · intro h
    have h' : 3 * a < 4 * b := by omega
    have e1 : 2 * c < a + 2 * b := hL.mpr h'
    have e2 : ¬ (2 * c ≤ 2 * a + b) := fun hcon => by have := hRle.mp hcon; omega
    exact ⟨by simp only [invB1]; omega, by simp only [invB1]; omega,
      by simpa [invB1] using hpos⟩

end EnergyAscent

namespace EnergyAscent

theorem branch_two_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) :
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ↔
      (3 * b < 4 * a ∧ 3 * a < 4 * b) := by
  have hL := EnergyAscent.cond_left_iff ha hb hc hpt
  have hR := EnergyAscent.cond_right_iff ha hb hc hpt
  have hpos := parent_hyp_pos a b c ha hb hc hpt
  constructor
  · rintro ⟨h1, h2, -⟩
    simp only [invB2] at h1 h2
    exact ⟨hR.mp (by omega), hL.mp (by omega)⟩
  · rintro ⟨h1, h2⟩
    have e1 := hL.mpr h2
    have e2 := hR.mpr h1
    refine ⟨by simp only [invB2]; omega, by simp only [invB2]; omega, ?_⟩
    simpa [invB2] using hpos

end EnergyAscent

namespace EnergyAscent

theorem branch_three_iff {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) :
    (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) ↔
      4 * b < 3 * a := by
  have hR := EnergyAscent.cond_right_iff ha hb hc hpt
  have hLle := EnergyAscent.cond_left_le_iff ha hb hc hpt
  have hpos := parent_hyp_pos a b c ha hb hc hpt
  constructor
  · rintro ⟨h1, -, -⟩
    simp only [invB3] at h1
    have hnot : ¬ (3 * a ≤ 4 * b) := fun hcon => by have := hLle.mpr hcon; omega
    omega
  · intro h
    have h' : 3 * b < 4 * a := by omega
    have e1 : 2 * c < 2 * a + b := hR.mpr h'
    have e2 : ¬ (2 * c ≤ a + 2 * b) := fun hcon => by have := hLle.mp hcon; omega
    exact ⟨by simp only [invB3]; omega, by simp only [invB3]; omega,
      by simpa [invB3] using hpos⟩

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_eq_zero_iff (a b : ℤ) :
    branchLetter a b = 0 ↔ 4 * a < 3 * b := by
  unfold branchLetter
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_eq_two_iff {a b : ℤ} (ha : 0 < a) :
    branchLetter a b = 2 ↔ 4 * b < 3 * a := by
  unfold branchLetter
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · exact ⟨fun _ => h2, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_eq_one_iff (a b : ℤ) :
    branchLetter a b = 1 ↔ (3 * b ≤ 4 * a ∧ 3 * a ≤ 4 * b) := by
  unfold branchLetter
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by omega)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 (by omega)⟩
  · exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => rfl⟩

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_ratio_invariant {a b a' b' : ℤ} (hb : 0 < b) (hb' : 0 < b')
    (h : a * b' = a' * b) : branchLetter a b = branchLetter a' b' := by
  have h1 : 4 * a < 3 * b ↔ 4 * a' < 3 * b' := by
    constructor <;> intro hlt
    · nlinarith
    · nlinarith
  have h2 : 4 * b < 3 * a ↔ 4 * b' < 3 * a' := by
    constructor <;> intro hlt
    · nlinarith
    · nlinarith
  unfold branchLetter
  by_cases hA : 4 * a < 3 * b
  · simp [hA, h1.mp hA]
  · have hA' : ¬ (4 * a' < 3 * b') := fun hc => hA (h1.mpr hc)
    by_cases hB : 4 * b < 3 * a
    · simp [hA, hA', hB, h2.mp hB]
    · have hB' : ¬ (4 * b' < 3 * a') := fun hc => hB (h2.mpr hc)
      simp [hA, hA', hB, hB']

end EnergyAscent

namespace EnergyAscent

theorem B1_isPT {a b c : ℤ} (hpt : IsPT a b c) :
    IsPT (B1 a b c).1 (B1 a b c).2.1 (B1 a b c).2.2 := by
  unfold IsPT B1 at *; simp only; linear_combination hpt

end EnergyAscent

namespace EnergyAscent

theorem B2_isPT {a b c : ℤ} (hpt : IsPT a b c) :
    IsPT (B2 a b c).1 (B2 a b c).2.1 (B2 a b c).2.2 := by
  unfold IsPT B2 at *; simp only; linear_combination hpt

end EnergyAscent

namespace EnergyAscent

theorem B3_isPT {a b c : ℤ} (hpt : IsPT a b c) :
    IsPT (B3 a b c).1 (B3 a b c).2.1 (B3 a b c).2.2 := by
  unfold IsPT B3 at *; simp only; linear_combination hpt

end EnergyAscent

namespace EnergyAscent

theorem invB1_B1 (a b c : ℤ) :
    invB1 (B1 a b c).1 (B1 a b c).2.1 (B1 a b c).2.2 = (a, b, c) := by
  simp only [invB1, B1, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

end EnergyAscent

namespace EnergyAscent

theorem invB2_B2 (a b c : ℤ) :
    invB2 (B2 a b c).1 (B2 a b c).2.1 (B2 a b c).2.2 = (a, b, c) := by
  simp only [invB2, B2, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

end EnergyAscent

namespace EnergyAscent

theorem invB3_B3 (a b c : ℤ) :
    invB3 (B3 a b c).1 (B3 a b c).2.1 (B3 a b c).2.2 = (a, b, c) := by
  simp only [invB3, B3, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_B1 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : branchLetter (B1 a b c).1 (B1 a b c).2.1 = 0 := by
  have hlt := EnergyAscent.hyp_lt_sum ha hb hc hpt
  rw [EnergyAscent.branchLetter_eq_zero_iff]
  simp only [B1]
  omega

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_B2 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : branchLetter (B2 a b c).1 (B2 a b c).2.1 = 1 := by
  have h1 : a < c := EnergyAscent.leg_lt_hyp hb hc hpt
  have h2 : b < c := EnergyAscent.leg_lt_hyp ha hc (by unfold IsPT at *; linarith [hpt])
  rw [EnergyAscent.branchLetter_eq_one_iff]
  simp only [B2]
  omega

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_B3 {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : branchLetter (B3 a b c).1 (B3 a b c).2.1 = 2 := by
  have hlt := EnergyAscent.hyp_lt_sum ha hb hc hpt
  have hac : a < c := EnergyAscent.leg_lt_hyp hb hc hpt
  have hA : 0 < (B3 a b c).1 := by simp only [B3]; omega
  rw [EnergyAscent.branchLetter_eq_two_iff hA]
  simp only [B3]
  omega

end EnergyAscent

namespace EnergyAscent

theorem no_boundary {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : 5 < c) (hprim : Int.gcd a b = 1) :
    4 * a ≠ 3 * b ∧ 4 * b ≠ 3 * a := by
  have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hprim
  constructor
  · intro h
    have hda : a ∣ 3 := hcop.dvd_of_dvd_mul_right ⟨4, by linarith⟩
    have hdb : b ∣ 4 := hcop.symm.dvd_of_dvd_mul_right ⟨3, by linarith⟩
    have ha3 : a ≤ 3 := Int.le_of_dvd (by norm_num) hda
    have hb4 : b ≤ 4 := Int.le_of_dvd (by norm_num) hdb
    unfold IsPT at hpt
    nlinarith
  · intro h
    have hdb : b ∣ 3 := hcop.symm.dvd_of_dvd_mul_right ⟨4, by linarith⟩
    have hda : a ∣ 4 := hcop.dvd_of_dvd_mul_right ⟨3, by linarith⟩
    have hb3 : b ≤ 3 := Int.le_of_dvd (by norm_num) hdb
    have ha4 : a ≤ 4 := Int.le_of_dvd (by norm_num) hda
    unfold IsPT at hpt
    nlinarith

end EnergyAscent

namespace EnergyAscent

theorem branchLetter_eq_descent {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : 5 < c) (hprim : Int.gcd a b = 1) :
    (branchLetter a b = 0 ↔
        (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2)) ∧
    (branchLetter a b = 1 ↔
        (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2)) ∧
    (branchLetter a b = 2 ↔
        (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2)) := by
  obtain ⟨hn1, hn2⟩ := EnergyAscent.no_boundary ha hb hc hpt hc5 hprim
  refine ⟨?_, ?_, ?_⟩
  · rw [EnergyAscent.branch_one_iff ha hb hc hpt, EnergyAscent.branchLetter_eq_zero_iff]
  · rw [EnergyAscent.branch_two_iff ha hb hc hpt, EnergyAscent.branchLetter_eq_one_iff]
    omega
  · rw [EnergyAscent.branch_three_iff ha hb hc hpt, EnergyAscent.branchLetter_eq_two_iff ha]

end EnergyAscent

namespace EnergyAscent

theorem branch_trichotomy {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : 5 < c) (hprim : Int.gcd a b = 1) :
    (4 * a < 3 * b ∧ ¬(3 * b < 4 * a ∧ 3 * a < 4 * b) ∧ ¬(4 * b < 3 * a)) ∨
    (¬(4 * a < 3 * b) ∧ (3 * b < 4 * a ∧ 3 * a < 4 * b) ∧ ¬(4 * b < 3 * a)) ∨
    (¬(4 * a < 3 * b) ∧ ¬(3 * b < 4 * a ∧ 3 * a < 4 * b) ∧ 4 * b < 3 * a) := by
  obtain ⟨hn1, hn2⟩ := EnergyAscent.no_boundary ha hb hc hpt hc5 hprim
  omega

end EnergyAscent

namespace EnergyAscent

theorem sqrt_le_mid {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p * q) ≤ (p + q) / 2 := by
  have h1 : p * q ≤ ((p + q) / 2) ^ 2 := by nlinarith [sq_nonneg (p - q)]
  calc Real.sqrt (p * q) ≤ Real.sqrt (((p + q) / 2) ^ 2) := Real.sqrt_le_sqrt h1
    _ = (p + q) / 2 := Real.sqrt_sq (by linarith)

end EnergyAscent

namespace EnergyAscent

theorem fermatOffset_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ fermatOffset p q := by
  have := EnergyAscent.sqrt_le_mid hp hq
  unfold fermatOffset; linarith

end EnergyAscent

namespace EnergyAscent

theorem fermatOffset_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    fermatOffset p q * ((p + q) / 2 + Real.sqrt (p * q)) = ((q - p) / 2) ^ 2 := by
  have hr : Real.sqrt (p * q) ^ 2 = p * q := Real.sq_sqrt (by positivity)
  unfold fermatOffset
  nlinarith [hr]

end EnergyAscent

namespace EnergyAscent

theorem fermatOffset_lower {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (q - p) ^ 2 / (4 * (p + q)) ≤ fermatOffset p q := by
  have hle := EnergyAscent.sqrt_le_mid hp.le hq.le
  have hnn := EnergyAscent.fermatOffset_nonneg hp.le hq.le
  have hid := EnergyAscent.fermatOffset_mul hp.le hq.le
  have hsum : (0 : ℝ) < 4 * (p + q) := by linarith
  rw [div_le_iff₀ hsum]
  nlinarith [hnn, hle, hid]

end EnergyAscent

namespace EnergyAscent

theorem fermatOffset_upper {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    fermatOffset p q ≤ (q - p) ^ 2 / (8 * Real.sqrt (p * q)) := by
  have hrpos : 0 < Real.sqrt (p * q) := Real.sqrt_pos.mpr (by positivity)
  have hnn := EnergyAscent.fermatOffset_nonneg hp.le hq.le
  have hle := EnergyAscent.sqrt_le_mid hp.le hq.le
  have hid := EnergyAscent.fermatOffset_mul hp.le hq.le
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hnn, hle, hid]

end EnergyAscent

namespace EnergyAscent

theorem fermatOffset_scale {p q l : ℝ} (hl : 0 ≤ l) :
    fermatOffset (l * p) (l * q) = l * fermatOffset p q := by
  unfold fermatOffset
  have : l * p * (l * q) = l ^ 2 * (p * q) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hl]
  ring

end EnergyAscent

namespace EnergyAscent

theorem window_hit_ratio_bound {p q W : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hhit : fermatOffset p q ≤ W) : (q - p) ^ 2 ≤ 4 * W * (p + q) := by
  have h := EnergyAscent.fermatOffset_lower hp hq
  have hsum : (0 : ℝ) < 4 * (p + q) := by linarith
  rw [div_le_iff₀ hsum] at h
  nlinarith [h, hhit]

end EnergyAscent

namespace EnergyAscent

theorem hit_implies_middle_band {p q W : ℤ} (hp : 0 < p) (hpq : p ≤ q)
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

end EnergyAscent

namespace EnergyAscent

theorem window_hit_determines_berggren_letter {a b c W : ℤ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hpt : IsPT a b c)
    (hprim : Int.gcd a b = 1) (hW : 0 < W) (hscale : 112 * W ≤ b)
    (hhit : fermatOffset (a : ℝ) (b : ℝ) ≤ (W : ℝ)) :
    branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbc : b < c := by unfold IsPT at hpt; nlinarith
  have hc5 : 5 < c := by omega
  obtain ⟨hne1, hne2⟩ := EnergyAscent.no_boundary ha hb hc hpt hc5 hprim
  obtain ⟨h1, h2⟩ := EnergyAscent.hit_implies_middle_band ha hab hscale hhit
  exact ⟨(EnergyAscent.branchLetter_eq_one_iff a b).mpr ⟨h1, h2⟩,
    (EnergyAscent.branch_two_iff ha hb hc hpt).mpr ⟨by omega, by omega⟩⟩

end EnergyAscent

namespace EnergyAscent

theorem balanced_implies_hit {p q W : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : (q - p) ^ 2 ≤ 8 * W * Real.sqrt (p * q)) : fermatOffset p q ≤ W := by
  have hrpos : 0 < Real.sqrt (p * q) := Real.sqrt_pos.mpr (by positivity)
  have hup := EnergyAscent.fermatOffset_upper hp hq
  have : (q - p) ^ 2 / (8 * Real.sqrt (p * q)) ≤ W := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h]
  linarith

end EnergyAscent

namespace EnergyAscent

theorem hits_exist_unbounded (W : ℤ) (hW : 0 < W) (S : ℤ) :
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
  refine EnergyAscent.balanced_implies_hit (by linarith) (by linarith) ?_
  have hone : ((p : ℝ) + 1 - p) ^ 2 = 1 := by ring
  rw [hone]
  nlinarith [hsq, hWR]

end EnergyAscent

namespace EnergyAscent

theorem hit_of_quartic_criterion {p q W : ℤ} (hp : 0 < p) (hq : 0 < q) (hW : 0 < W)
    (h : (q - p) ^ 4 ≤ 64 * W ^ 2 * (p * q)) :
    fermatOffset (p : ℝ) (q : ℝ) ≤ (W : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hR : ((q : ℝ) - p) ^ 4 ≤ 64 * (W : ℝ) ^ 2 * ((p : ℝ) * q) := by exact_mod_cast h
  have hs : (0 : ℝ) ≤ Real.sqrt ((p : ℝ) * q) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((p : ℝ) * q) ^ 2 = (p : ℝ) * q := Real.sq_sqrt (by positivity)
  refine EnergyAscent.balanced_implies_hit hpR hqR ?_
  by_contra hcon
  push_neg at hcon
  have hA : (0 : ℝ) ≤ 8 * (W : ℝ) * Real.sqrt ((p : ℝ) * q) := by positivity
  have h2 := mul_self_lt_mul_self hA hcon
  nlinarith [h2, hsq, hR]

end EnergyAscent

namespace EnergyAscent

theorem threshold_sharp :
    ∃ p q c W : ℤ, 0 < p ∧ p ≤ q ∧ 0 < c ∧ IsPT p q c ∧ Int.gcd p q = 1 ∧
      0 < W ∧ 110 * W ≤ q ∧ fermatOffset (p : ℝ) (q : ℝ) ≤ (W : ℝ) ∧
      branchLetter p q ≠ 1 := by
  refine ⟨752604, 1004653, 1255285, 9133, by norm_num, by norm_num, by norm_num, ?_,
    by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · unfold IsPT; norm_num
  · exact EnergyAscent.hit_of_quartic_criterion (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have h0 : branchLetter (752604 : ℤ) (1004653 : ℤ) = 0 :=
      (EnergyAscent.branchLetter_eq_zero_iff _ _).mpr (by norm_num)
    rw [h0]
    decide

end EnergyAscent

namespace EnergyAscent

@[simp] theorem spine_zero : spine 0 = (3, 4, 5) := rfl

end EnergyAscent

namespace EnergyAscent

theorem spine_succ (n : ℕ) :
    spine (n + 1) = B2 (spine n).1 (spine n).2.1 (spine n).2.2 := rfl

end EnergyAscent

namespace EnergyAscent

theorem spine_invariants (n : ℕ) :
    0 < (spine n).1 ∧ 0 < (spine n).2.1 ∧ 0 < (spine n).2.2 ∧
      IsPT (spine n).1 (spine n).2.1 (spine n).2.2 ∧
      ((spine n).1 - (spine n).2.1) ^ 2 = 1 ∧
      (n : ℤ) + 5 ≤ (spine n).2.2 := by
  induction n with
  | zero => refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num, by norm_num⟩
            unfold IsPT; norm_num
  | succ n ih =>
    obtain ⟨ha, hb, hc, hpt, hgap, hgrow⟩ := ih
    have hlt : (spine n).2.2 < (spine n).1 + (spine n).2.1 := EnergyAscent.hyp_lt_sum ha hb hc hpt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [EnergyAscent.spine_succ]; simp only [B2]; omega
    · rw [EnergyAscent.spine_succ]; simp only [B2]; omega
    · rw [EnergyAscent.spine_succ]; simp only [B2]; omega
    · rw [EnergyAscent.spine_succ]; exact EnergyAscent.B2_isPT hpt
    · rw [EnergyAscent.spine_succ]; simp only [B2]; linear_combination hgap
    · rw [EnergyAscent.spine_succ]; simp only [B2]; push_cast; omega

end EnergyAscent

namespace EnergyAscent

theorem spine_gap (n : ℕ) : ((spine n).1 - (spine n).2.1) ^ 2 = 1 :=
  (EnergyAscent.spine_invariants n).2.2.2.2.1

end EnergyAscent

namespace EnergyAscent

theorem spine_primitive (n : ℕ) : Int.gcd (spine n).1 (spine n).2.1 = 1 := by
  have h := EnergyAscent.spine_gap n
  have hcop : IsCoprime (spine n).1 (spine n).2.1 :=
    ⟨(spine n).1 - (spine n).2.1, -((spine n).1 - (spine n).2.1), by linear_combination h⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp hcop

end EnergyAscent

namespace EnergyAscent

theorem unit_gap_hit {p : ℤ} (hp : 0 < p) :
    fermatOffset (p : ℝ) ((p : ℝ) + 1) ≤ (1 : ℝ) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : (1 : ℝ) ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) + 1)) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (p : ℝ) * ((p : ℝ) + 1) by nlinarith)
    rwa [Real.sqrt_one] at h
  refine EnergyAscent.balanced_implies_hit (by linarith) (by linarith) ?_
  have hone : ((p : ℝ) + 1 - p) ^ 2 = 1 := by ring
  rw [hone]
  nlinarith [hsq]

end EnergyAscent

namespace EnergyAscent

theorem spine_sorted (n : ℕ) :
    ∃ p c : ℤ, 0 < p ∧ 0 < c ∧ IsPT p (p + 1) c ∧ Int.gcd p (p + 1) = 1 ∧
      (n : ℤ) + 5 ≤ c ∧ c < p + (p + 1) := by
  obtain ⟨ha, hb, hc, hpt, hgap, hgrow⟩ := EnergyAscent.spine_invariants n
  set a := (spine n).1
  set b := (spine n).2.1
  set c := (spine n).2.2
  have hlt : c < a + b := EnergyAscent.hyp_lt_sum ha hb hc hpt
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

end EnergyAscent

namespace EnergyAscent

theorem bridge_nonvacuous (S : ℤ) :
    ∃ a b c : ℤ, S < b ∧ 112 ≤ b ∧ 0 < a ∧ a ≤ b ∧ 0 < c ∧ IsPT a b c ∧
      Int.gcd a b = 1 ∧ fermatOffset (a : ℝ) (b : ℝ) ≤ (1 : ℝ) ∧
      branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max (2 * S) 224 ≤ (n : ℤ) := ⟨(max (2 * S) 224).toNat, by omega⟩
  obtain ⟨p, c, hp, hc, hpt, hcop, hgrow, hsum⟩ := EnergyAscent.spine_sorted n
  have hS : 2 * S ≤ (n : ℤ) := le_trans (le_max_left _ _) hn
  have h224 : (224 : ℤ) ≤ (n : ℤ) := le_trans (le_max_right _ _) hn
  have hpbig : 112 ≤ p := by omega
  have hhit : fermatOffset (p : ℝ) ((p : ℝ) + 1) ≤ (1 : ℝ) := EnergyAscent.unit_gap_hit hp
  have hcast : ((p + 1 : ℤ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  obtain ⟨hletter, hparent⟩ :=
    window_hit_determines_berggren_letter (a := p) (b := p + 1) (c := c) (W := 1)
      hp (by omega) hc hpt hcop (by norm_num) (by omega) (by rw [hcast]; simpa using hhit)
  exact ⟨p, p + 1, c, by omega, by omega, hp, by omega, hc, hpt, hcop,
    by rw [hcast]; simpa using hhit, hletter, hparent⟩

end EnergyAscent


theorem solution (S : ℤ) :
    ∃ a b c : ℤ, S < b ∧ 112 ≤ b ∧ 0 < a ∧ a ≤ b ∧ 0 < c ∧ IsPT a b c ∧
      Int.gcd a b = 1 ∧ fermatOffset (a : ℝ) (b : ℝ) ≤ (1 : ℝ) ∧
      branchLetter a b = 1 ∧
      (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, max (2 * S) 224 ≤ (n : ℤ) := ⟨(max (2 * S) 224).toNat, by omega⟩
  obtain ⟨p, c, hp, hc, hpt, hcop, hgrow, hsum⟩ := EnergyAscent.spine_sorted n
  have hS : 2 * S ≤ (n : ℤ) := le_trans (le_max_left _ _) hn
  have h224 : (224 : ℤ) ≤ (n : ℤ) := le_trans (le_max_right _ _) hn
  have hpbig : 112 ≤ p := by omega
  have hhit : fermatOffset (p : ℝ) ((p : ℝ) + 1) ≤ (1 : ℝ) := EnergyAscent.unit_gap_hit hp
  have hcast : ((p + 1 : ℤ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
  obtain ⟨hletter, hparent⟩ :=
    window_hit_determines_berggren_letter (a := p) (b := p + 1) (c := c) (W := 1)
      hp (by omega) hc hpt hcop (by norm_num) (by omega) (by rw [hcast]; simpa using hhit)
  exact ⟨p, p + 1, c, by omega, by omega, hp, by omega, hc, hpt, hcop,
    by rw [hcast]; simpa using hhit, hletter, hparent⟩

#print axioms solution
