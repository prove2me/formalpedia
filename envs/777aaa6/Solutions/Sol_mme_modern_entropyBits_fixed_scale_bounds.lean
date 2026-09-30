-- Prove2me | solution 1 for mme_modern_entropyBits_fixed_scale_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T08:25:01.539102+00:00
-- url     : https://prove2.me/submissions/c0a038d3-de19-412d-bae1-73b73ce03f77

import Theorems.Thm_mme_fixed_scale_log_interval_sound
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace MME.DyadicLog

private theorem unitLog_valid {S p d n : ℕ} (hS : 0 < S) (hd : 0 < d)
    (hlo : d ≤ p) (hhi : p ≤ 2 * d) :
    (unitLog S p d n).Valid S (Real.log ((p : ℝ) / (d : ℝ))) := by
  have h := mme_fixed_scale_log_interval_sound (S := S) (p := p) (d := d)
    (k := 0) (n := n) hS (hd.trans_le hlo) hd (by simpa using hlo) (by simpa using hhi)
  simpa [scaledLog, SignedInterval.Valid, Interval.Valid] using h

theorem entropyCell_valid {S p d k n : ℕ} (hS : 0 < S) (hd : 0 < d)
    (hnorm : p = 0 ∨ (d ≤ p * 2 ^ k ∧ p * 2 ^ k ≤ 2 * d)) :
    (entropyCell S p d k n).Valid (S * d)
      (Real.negMulLog ((p : ℝ) / (d : ℝ))) := by
  by_cases hp : p = 0
  · subst p
    simp [entropyCell, SignedInterval.Valid]
  · have hn := hnorm.resolve_left hp
    have hv := mme_fixed_scale_log_interval_sound (n := n) hS (Nat.pos_of_ne_zero hp) hd hn.1 hn.2
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 := mul_le_mul_of_nonpos_left hv.2 (neg_nonpos.mpr (Nat.cast_nonneg p (α := ℝ)))
    have h2 := mul_le_mul_of_nonpos_left hv.1 (neg_nonpos.mpr (Nat.cast_nonneg p (α := ℝ)))
    have he : ((S * d : ℕ) : ℝ) * Real.negMulLog ((p : ℝ) / d) =
        -(p : ℝ) * ((S : ℝ) * Real.log ((p : ℝ) / d)) := by
      simp only [Real.negMulLog, Nat.cast_mul]
      field_simp
    simp only [entropyCell, hp, ↓reduceIte, SignedInterval.Valid,
      Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    rw [he]
    exact ⟨h1, h2⟩

/-- An integer-only entropy evaluator is sound for every table passing its
range-reduction check. The returned interval has common scale S*d. -/
theorem entropyInterval_valid {S d n : ℕ} (hS : 0 < S) (hd : 0 < d)
    (cells : List (ℕ × ℕ)) (hcheck : rangeReductionCheck d cells = true) :
    (entropyInterval S d n cells).Valid (S * d)
      ((cells.map (fun cell ↦ Real.negMulLog ((cell.1 : ℝ) / (d : ℝ)))).sum) := by
  induction cells with
  | nil => simp [entropyInterval, SignedInterval.Valid]
  | cons cell rest ih =>
      rcases cell with ⟨p, k⟩
      have hc : (p = 0 ∨ (d ≤ p * 2 ^ k ∧ p * 2 ^ k ≤ 2 * d)) ∧
          rangeReductionCheck d rest = true := by
        simpa [rangeReductionCheck] using hcheck
      have ha := entropyCell_valid (n := n) hS hd hc.1
      have hb := ih hc.2
      simp only [entropyInterval, List.map_cons, List.sum_cons, SignedInterval.Valid,
        Int.cast_add]
      simp only [SignedInterval.Valid] at ha hb
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Certify a strict lower bound on base-two entropy using only an integer
comparison after evaluating the table and log 2. -/
theorem entropyBits_lower_of_check {S d n q r : ℕ} (hS : 0 < S) (hd : 0 < d)
    (hr : 0 < r) (cells : List (ℕ × ℕ))
    (hcheck : rangeReductionCheck d cells = true)
    (hmargin : (q : ℤ) * d * (unitLog S 2 1 n).hi <
      (r : ℤ) * (entropyInterval S d n cells).lo) :
    (q : ℝ) / (r : ℝ) <
      ((cells.map (fun cell ↦ Real.negMulLog ((cell.1 : ℝ) / (d : ℝ)))).sum) /
        Real.log 2 := by
  have he := entropyInterval_valid (n := n) hS hd cells hcheck
  have hl := unitLog_valid (p := 2) (d := 1) (n := n) hS (by omega)
    (by omega) (by omega)
  simp only [Interval.Valid, Nat.cast_ofNat, Nat.cast_one, div_one] at hl
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : (q : ℝ) * (d : ℝ) * ((unitLog S 2 1 n).hi : ℝ) <
      (r : ℝ) * ((entropyInterval S d n cells).lo : ℝ) := by
    exact_mod_cast hmargin
  have hb := mul_le_mul_of_nonneg_left hl.2
    (mul_nonneg (Nat.cast_nonneg q (α := ℝ)) hd'.le)
  have ha := mul_le_mul_of_nonneg_left he.1 hr'.le
  rw [div_lt_div_iff₀ hr' hlog]
  have hsd : (0 : ℝ) < (S : ℝ) * d := mul_pos hs hd'
  push_cast at ha
  apply (mul_lt_mul_iff_right₀ hsd).mp
  convert hb.trans_lt (hm.trans_le ha) using 1 <;> ring

/-- Certify a strict upper bound on base-two entropy. -/
theorem entropyBits_upper_of_check {S d n q r : ℕ} (hS : 0 < S) (hd : 0 < d)
    (hr : 0 < r) (cells : List (ℕ × ℕ))
    (hcheck : rangeReductionCheck d cells = true)
    (hmargin : (r : ℤ) * (entropyInterval S d n cells).hi <
      (q : ℤ) * d * (unitLog S 2 1 n).lo) :
    ((cells.map (fun cell ↦ Real.negMulLog ((cell.1 : ℝ) / (d : ℝ)))).sum) /
        Real.log 2 < (q : ℝ) / (r : ℝ) := by
  have he := entropyInterval_valid (n := n) hS hd cells hcheck
  have hl := unitLog_valid (p := 2) (d := 1) (n := n) hS (by omega)
    (by omega) (by omega)
  simp only [Interval.Valid, Nat.cast_ofNat, Nat.cast_one, div_one] at hl
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : (r : ℝ) * ((entropyInterval S d n cells).hi : ℝ) <
      (q : ℝ) * (d : ℝ) * ((unitLog S 2 1 n).lo : ℝ) := by
    exact_mod_cast hmargin
  have hb := mul_le_mul_of_nonneg_left hl.1
    (mul_nonneg (Nat.cast_nonneg q (α := ℝ)) hd'.le)
  have ha := mul_le_mul_of_nonneg_left he.2 hr'.le
  rw [div_lt_div_iff₀ hlog hr']
  have hsd : (0 : ℝ) < (S : ℝ) * d := mul_pos hs hd'
  push_cast at ha
  apply (mul_lt_mul_iff_right₀ hsd).mp
  convert ha.trans_lt (hm.trans_le hb) using 1 <;> ring

end MME.DyadicLog

open MME.DyadicLog

theorem solution {m S d n qL rL qU rU : ℕ}
    (hS : 0 < S) (hd : 0 < d) (hrL : 0 < rL) (hrU : 0 < rU)
    (counts shifts : Fin m → ℕ)
    (hcheck : rangeReductionCheck d (List.ofFn (fun i ↦ (counts i, shifts i))) = true)
    (hlower : (qL : ℤ) * d * (unitLog S 2 1 n).hi <
      (rL : ℤ) * (entropyInterval S d n
        (List.ofFn (fun i ↦ (counts i, shifts i)))).lo)
    (hupper : (rU : ℤ) * (entropyInterval S d n
        (List.ofFn (fun i ↦ (counts i, shifts i)))).hi <
      (qU : ℤ) * d * (unitLog S 2 1 n).lo) :
    (qL : ℝ) / (rL : ℝ) < mme_modern_entropyBits (fun i ↦ (counts i : ℝ) / d) ∧
      mme_modern_entropyBits (fun i ↦ (counts i : ℝ) / d) < (qU : ℝ) / (rU : ℝ) := by
  constructor
  · simpa [mme_modern_entropyBits, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
      entropyBits_lower_of_check hS hd hrL
        (List.ofFn (fun i ↦ (counts i, shifts i))) hcheck hlower
  · simpa [mme_modern_entropyBits, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
      entropyBits_upper_of_check hS hd hrU
        (List.ofFn (fun i ↦ (counts i, shifts i))) hcheck hupper
