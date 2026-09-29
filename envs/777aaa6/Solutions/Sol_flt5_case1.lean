-- Prove2me | solution 1 for flt5_case1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T09:31:50.424015+00:00
-- url     : https://prove2.me/submissions/f8b4a578-a793-420c-8434-8c02c67a274a

import Theorems.Thm_flt5_case1
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (ha5 : ¬(5 : ℤ) ∣ a) (hb5 : ¬(5 : ℤ) ∣ b) (hc5 : ¬(5 : ℤ) ∣ c) : False := by
  -- 5th powers mod 25 for non-multiples of 5 are in {1,7,18,24}; no two sum to another.
  -- Multiples of 5 in ZMod 25 are {0, 5, 10, 15, 20}.
  have key : ∀ x y z : ZMod 25,
      x ≠ 0 → x ≠ 5 → x ≠ 10 → x ≠ 15 → x ≠ 20 →
      y ≠ 0 → y ≠ 5 → y ≠ 10 → y ≠ 15 → y ≠ 20 →
      z ≠ 0 → z ≠ 5 → z ≠ 10 → z ≠ 15 → z ≠ 20 →
      x ^ 5 + y ^ 5 ≠ z ^ 5 := by decide
  -- Cast the equation to ZMod 25
  have heq25 : ((a : ℤ) : ZMod 25) ^ 5 + ((b : ℤ) : ZMod 25) ^ 5 = ((c : ℤ) : ZMod 25) ^ 5 := by
    have := congr_arg (Int.cast : ℤ → ZMod 25) h_eq
    push_cast at this; exact this
  -- Bridge: ¬(5 ∣ n) and (n : ZMod 25) = (k : ZMod 25) with 5 ∣ k gives a contradiction
  have ne_of_ndvd5 : ∀ (n : ℤ), ¬(5 : ℤ) ∣ n → ∀ (k : ℤ), (5 : ℤ) ∣ k →
      ((n : ℤ) : ZMod 25) ≠ ((k : ℤ) : ZMod 25) := by
    intro n hn k hk heq
    apply hn
    have h : ((n - k : ℤ) : ZMod 25) = 0 := by push_cast; rw [heq]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have h5 := dvd_trans (⟨5, by ring⟩ : (5 : ℤ) ∣ 25) h
    have hsum := dvd_add h5 hk
    rwa [show n - k + k = n from by ring] at hsum
  -- Non-divisibility conditions for a in ZMod 25
  have ha0  : ((a : ℤ) : ZMod 25) ≠ ((0  : ℤ) : ZMod 25) := ne_of_ndvd5 a ha5 0  ⟨0, by ring⟩
  have ha5n : ((a : ℤ) : ZMod 25) ≠ ((5  : ℤ) : ZMod 25) := ne_of_ndvd5 a ha5 5  ⟨1, by ring⟩
  have ha10 : ((a : ℤ) : ZMod 25) ≠ ((10 : ℤ) : ZMod 25) := ne_of_ndvd5 a ha5 10 ⟨2, by ring⟩
  have ha15 : ((a : ℤ) : ZMod 25) ≠ ((15 : ℤ) : ZMod 25) := ne_of_ndvd5 a ha5 15 ⟨3, by ring⟩
  have ha20 : ((a : ℤ) : ZMod 25) ≠ ((20 : ℤ) : ZMod 25) := ne_of_ndvd5 a ha5 20 ⟨4, by ring⟩
  -- Non-divisibility conditions for b in ZMod 25
  have hb0  : ((b : ℤ) : ZMod 25) ≠ ((0  : ℤ) : ZMod 25) := ne_of_ndvd5 b hb5 0  ⟨0, by ring⟩
  have hb5n : ((b : ℤ) : ZMod 25) ≠ ((5  : ℤ) : ZMod 25) := ne_of_ndvd5 b hb5 5  ⟨1, by ring⟩
  have hb10 : ((b : ℤ) : ZMod 25) ≠ ((10 : ℤ) : ZMod 25) := ne_of_ndvd5 b hb5 10 ⟨2, by ring⟩
  have hb15 : ((b : ℤ) : ZMod 25) ≠ ((15 : ℤ) : ZMod 25) := ne_of_ndvd5 b hb5 15 ⟨3, by ring⟩
  have hb20 : ((b : ℤ) : ZMod 25) ≠ ((20 : ℤ) : ZMod 25) := ne_of_ndvd5 b hb5 20 ⟨4, by ring⟩
  -- Non-divisibility conditions for c in ZMod 25
  have hc0  : ((c : ℤ) : ZMod 25) ≠ ((0  : ℤ) : ZMod 25) := ne_of_ndvd5 c hc5 0  ⟨0, by ring⟩
  have hc5n : ((c : ℤ) : ZMod 25) ≠ ((5  : ℤ) : ZMod 25) := ne_of_ndvd5 c hc5 5  ⟨1, by ring⟩
  have hc10 : ((c : ℤ) : ZMod 25) ≠ ((10 : ℤ) : ZMod 25) := ne_of_ndvd5 c hc5 10 ⟨2, by ring⟩
  have hc15 : ((c : ℤ) : ZMod 25) ≠ ((15 : ℤ) : ZMod 25) := ne_of_ndvd5 c hc5 15 ⟨3, by ring⟩
  have hc20 : ((c : ℤ) : ZMod 25) ≠ ((20 : ℤ) : ZMod 25) := ne_of_ndvd5 c hc5 20 ⟨4, by ring⟩
  -- Apply key lemma; numeral casts ((k : ℤ) : ZMod 25) = (k : ZMod 25) are definitionally equal
  exact key ((a : ℤ) : ZMod 25) ((b : ℤ) : ZMod 25) ((c : ℤ) : ZMod 25)
    ha0 ha5n ha10 ha15 ha20
    hb0 hb5n hb10 hb15 hb20
    hc0 hc5n hc10 hc15 hc20
    heq25
