-- Prove2me | solution 1 for lean_workbook_plus_71443
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:09.687135+00:00
-- url     : https://prove2.me/submissions/29949ff1-edce-4152-a16e-f7df96931bac

import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic

namespace SquareIndexEvenFloorRecurrence

theorem small_square_crossing {d : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) :
    ∃ k : ℕ, 0 < k ∧ 1 < d * (k : ℝ) ^ 2 ∧ d * (k : ℝ) ^ 2 ≤ 2 := by
  classical
  have hex : ∃ k : ℕ, 1 < d * (k : ℝ) ^ 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / d + 1)
    have hk1 : (1 : ℝ) < k := by linarith [one_div_pos.mpr hd]
    have hkd : 1 < d * k := by
      have h := (div_lt_iff₀ hd).mp (show 1 / d < (k : ℝ) by linarith)
      nlinarith
    refine ⟨k, ?_⟩
    exact hkd.trans_le (mul_le_mul_of_nonneg_left (by nlinarith :
      (k : ℝ) ≤ (k : ℝ) ^ 2) hd.le)
  let k := Nat.find hex
  have hk : 1 < d * (k : ℝ) ^ 2 := Nat.find_spec hex
  have hk3 : 3 ≤ k := by
    by_contra h
    have hlt : k < 3 := by omega
    interval_cases k <;> norm_num at hk <;> linarith
  have hprev : d * ((k - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
    exact le_of_not_gt (Nat.find_min hex (show k - 1 < k by omega))
  refine ⟨k, by omega, hk, ?_⟩
  by_cases he : k = 3
  · rw [he]
    norm_num
    linarith
  · have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by omega)
    rw [Nat.cast_sub (show 1 ≤ k by omega)] at hprev
    norm_num at hprev
    have hs : (k : ℝ) ^ 2 ≤ 2 * ((k : ℝ) - 1) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hd.le
    nlinarith

theorem near_even_square {a : ℝ} {m : ℤ}
    (hlo : 0 < (2 * m : ℤ) - a) (hhi : (2 * m : ℤ) - a ≤ 1 / 8) :
    ∃ k : ℕ, 0 < k ∧ Even ⌊(k : ℝ) ^ 2 * a⌋ := by
  obtain ⟨k, hk, hl, hu⟩ := small_square_crossing hlo hhi
  refine ⟨k, hk, ?_⟩
  have hf : ⌊(k : ℝ) ^ 2 * a⌋ = 2 * (m * (k : ℤ) ^ 2 - 1) := by
    apply Int.floor_eq_iff.mpr
    push_cast at *
    constructor <;> nlinarith
  rw [hf]
  exact even_two_mul _

theorem odd_floor_unique {x : ℝ} {m : ℤ} (hm : Even m)
    (hl : (m : ℝ) ≤ x) (hu : x < (m : ℝ) + 2) (h : ¬Even ⌊x⌋) :
    ⌊x⌋ = m + 1 := by
  have ha : m ≤ ⌊x⌋ := Int.le_floor.mpr hl
  have hb : ⌊x⌋ < m + 2 := Int.floor_lt.mpr (by exact_mod_cast hu)
  have hc := Int.odd_iff.mp (Int.not_even_iff_odd.mp h)
  have hm' := Int.even_iff.mp hm
  omega

theorem five_test_reduction {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2)
    (h1 : ¬Even ⌊r⌋) (h4 : ¬Even ⌊4 * r⌋) (h9 : ¬Even ⌊9 * r⌋)
    (h16 : ¬Even ⌊16 * r⌋) (h25 : ¬Even ⌊25 * r⌋) :
    (33 / 25 ≤ r ∧ r < 4 / 3) ∨
      (37 / 25 ≤ r ∧ r < 3 / 2) ∨ (49 / 25 ≤ r ∧ r < 2) := by
  have hf1 : ⌊r⌋ = 1 := odd_floor_unique (by decide : Even (0 : ℤ)) (by simpa using hr0)
    (by simpa using hr2) h1
  have hr1 : 1 ≤ r := by simpa [hf1] using Int.floor_le r
  have hp4 := Int.odd_iff.mp (Int.not_even_iff_odd.mp h4)
  have hl4 : 4 ≤ ⌊4 * r⌋ := Int.le_floor.mpr (by norm_num; linarith)
  have hu4 : ⌊4 * r⌋ < 8 := Int.floor_lt.mpr (by norm_num; linarith)
  have hc4 : ⌊4 * r⌋ = 5 ∨ ⌊4 * r⌋ = 7 := by omega
  have hp9 := Int.odd_iff.mp (Int.not_even_iff_odd.mp h9)
  rcases hc4 with he4 | he4
  · have hb4 := Int.floor_eq_iff.mp he4
    norm_num at hb4
    have hl9 : 11 ≤ ⌊9 * r⌋ := Int.le_floor.mpr (by norm_num; linarith)
    have hu9 : ⌊9 * r⌋ < 14 := Int.floor_lt.mpr (by norm_num; linarith)
    have hc9 : ⌊9 * r⌋ = 11 ∨ ⌊9 * r⌋ = 13 := by omega
    rcases hc9 with he9 | he9
    · have hb9 := Int.floor_eq_iff.mp he9
      norm_num at hb9
      have he16 : ⌊16 * r⌋ = 21 := odd_floor_unique
        (by decide : Even (20 : ℤ)) (by norm_num; linarith) (by norm_num; linarith) h16
      have hb16 := Int.floor_eq_iff.mp he16
      norm_num at hb16
      have he25 : ⌊25 * r⌋ = 33 := odd_floor_unique
        (by decide : Even (32 : ℤ)) (by norm_num; linarith) (by norm_num; linarith) h25
      have hb25 := Int.floor_eq_iff.mp he25
      norm_num at hb25
      left
      constructor <;> linarith
    · have hb9 := Int.floor_eq_iff.mp he9
      norm_num at hb9
      have he25 : ⌊25 * r⌋ = 37 := odd_floor_unique
        (by decide : Even (36 : ℤ)) (by norm_num; linarith) (by norm_num; linarith) h25
      have hb25 := Int.floor_eq_iff.mp he25
      norm_num at hb25
      right; left
      constructor <;> linarith
  · have hb4 := Int.floor_eq_iff.mp he4
    norm_num at hb4
    have hl9 : 15 ≤ ⌊9 * r⌋ := Int.le_floor.mpr (by norm_num; linarith)
    have hu9 : ⌊9 * r⌋ < 18 := Int.floor_lt.mpr (by norm_num; linarith)
    have hc9 : ⌊9 * r⌋ = 15 ∨ ⌊9 * r⌋ = 17 := by omega
    rcases hc9 with he9 | he9
    · have hb9 := Int.floor_eq_iff.mp he9
      norm_num at hb9
      have he16 : ⌊16 * r⌋ = 28 := Int.floor_eq_iff.mpr (by
        norm_num
        constructor <;> linarith)
      exact (h16 (by rw [he16]; decide)).elim
    · have hb9 := Int.floor_eq_iff.mp he9
      norm_num at hb9
      have he16 : ⌊16 * r⌋ = 31 := odd_floor_unique
        (by decide : Even (30 : ℤ)) (by norm_num; linarith) (by norm_num; linarith) h16
      have hb16 := Int.floor_eq_iff.mp he16
      norm_num at hb16
      have he25 : ⌊25 * r⌋ = 49 := odd_floor_unique
        (by decide : Even (48 : ℤ)) (by norm_num; linarith) (by norm_num; linarith) h25
      have hb25 := Int.floor_eq_iff.mp he25
      norm_num at hb25
      right; right
      constructor <;> linarith

theorem normalized_positive_witness {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2) :
    ∃ n : ℕ, 0 < n ∧ Even ⌊(n : ℝ) ^ 2 * r⌋ := by
  by_contra h
  push_neg at h
  have h1 := h 1 (by decide)
  have h4 := h 2 (by decide)
  have h9 := h 3 (by decide)
  have h16 := h 4 (by decide)
  have h25 := h 5 (by decide)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_pow, one_mul] at h1 h4 h9 h16 h25
  rcases five_test_reduction hr0 hr2 h1 h4 h9 h16 h25 with hb | hb | hb
  · obtain ⟨k, hk, he⟩ := near_even_square (a := 9 * r) (m := 6)
      (by norm_num; linarith [hb.2]) (by norm_num; linarith [hb.1])
    apply h (k * 3) (by omega)
    have hid : ((k * 3 : ℕ) : ℝ) ^ 2 * r = (k : ℝ) ^ 2 * (9 * r) := by
      push_cast
      ring
    rw [hid]
    exact he
  · obtain ⟨k, hk, he⟩ := near_even_square (a := 4 * r) (m := 3)
      (by norm_num; linarith [hb.2]) (by norm_num; linarith [hb.1])
    apply h (k * 2) (by omega)
    have hid : ((k * 2 : ℕ) : ℝ) ^ 2 * r = (k : ℝ) ^ 2 * (4 * r) := by
      push_cast
      ring
    rw [hid]
    exact he
  · obtain ⟨k, hk, he⟩ := near_even_square (a := r) (m := 1)
      (by norm_num; linarith [hb.2]) (by norm_num; linarith [hb.1])
    exact h k hk he

theorem positive_witness (a : ℝ) :
    ∃ n : ℕ, 0 < n ∧ Even ⌊(n : ℝ) ^ 2 * a⌋ := by
  let q : ℤ := ⌊a / 2⌋
  let r : ℝ := a - 2 * q
  have hq0 := Int.floor_le (a / 2)
  have hq1 := Int.lt_floor_add_one (a / 2)
  have hr0 : 0 ≤ r := by dsimp [r, q]; linarith
  have hr2 : r < 2 := by dsimp [r, q]; linarith
  obtain ⟨n, hn, he⟩ := normalized_positive_witness hr0 hr2
  refine ⟨n, hn, ?_⟩
  have hid : (n : ℝ) ^ 2 * a = (n : ℝ) ^ 2 * r +
      ((2 * q * (n : ℤ) ^ 2 : ℤ) : ℝ) := by dsimp [r]; push_cast; ring
  rw [hid, Int.floor_add_intCast]
  exact he.add (by refine ⟨q * (n : ℤ) ^ 2, ?_⟩; ring)

theorem arbitrarily_large (a : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Even ⌊(n : ℝ) ^ 2 * a⌋ := by
  obtain ⟨k, hk, he⟩ := positive_witness (((N + 1 : ℕ) : ℝ) ^ 2 * a)
  refine ⟨k * (N + 1), by nlinarith, ?_⟩
  have hid : ((k * (N + 1) : ℕ) : ℝ) ^ 2 * a =
      (k : ℝ) ^ 2 * (((N + 1 : ℕ) : ℝ) ^ 2 * a) := by
    push_cast
    ring
  rw [hid]
  exact he

theorem infinitely_many (a : ℝ) :
    Set.Infinite {n : ℕ | 0 < n ∧ Even ⌊(n : ℝ) ^ 2 * a⌋} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, he⟩ := arbitrarily_large a N
  exact ⟨n, ⟨by omega, he⟩, hn⟩

end SquareIndexEvenFloorRecurrence

theorem solution (a : ℝ) (_h : a > 0) : ∃ n : ℕ, Even (Int.floor (n ^ 2 * a)) := by
  obtain ⟨n, _, hn⟩ := SquareIndexEvenFloorRecurrence.positive_witness a
  exact ⟨n, hn⟩

#print axioms SquareIndexEvenFloorRecurrence.small_square_crossing
#print axioms SquareIndexEvenFloorRecurrence.near_even_square
#print axioms SquareIndexEvenFloorRecurrence.odd_floor_unique
#print axioms SquareIndexEvenFloorRecurrence.five_test_reduction
#print axioms SquareIndexEvenFloorRecurrence.normalized_positive_witness
#print axioms SquareIndexEvenFloorRecurrence.positive_witness
#print axioms SquareIndexEvenFloorRecurrence.arbitrarily_large
#print axioms SquareIndexEvenFloorRecurrence.infinitely_many
#print axioms solution
