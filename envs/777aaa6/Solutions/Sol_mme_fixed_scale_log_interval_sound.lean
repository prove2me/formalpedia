-- Prove2me | solution 1 for mme_fixed_scale_log_interval_sound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T08:24:57.01858+00:00
-- url     : https://prove2.me/submissions/1a1677da-ec25-47a9-8971-2b70500c7fb2

import Definitions.Def_mme_dyadic_log_interval
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open BigOperators
set_option autoImplicit false

namespace MME.DyadicLog

private theorem nat_div_lower (a d : ℕ) :
    ((a / d : ℕ) : ℝ) * (d : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast Nat.div_mul_le_self a d

private theorem nat_div_upper (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) ≤ ((a / d + 1 : ℕ) : ℝ) * (d : ℝ) := by
  have h := (Nat.lt_mul_div_succ a hd).le
  exact_mod_cast (by simpa [Nat.mul_comm] using h : a ≤ (a / d + 1) * d)

theorem valid_nonneg {S : ℕ} (hS : 0 < S) {a : Interval} {x : ℝ}
    (hx : a.Valid S x) : 0 ≤ x := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have h := (Nat.cast_nonneg a.lo (α := ℝ)).trans hx.1
  exact nonneg_of_mul_nonneg_right h hs

theorem zero_valid (S : ℕ) : zero.Valid S 0 := by
  simp [zero, Interval.Valid]

theorem add_valid {S : ℕ} {a b : Interval} {x y : ℝ}
    (hx : a.Valid S x) (hy : b.Valid S y) : (add a b).Valid S (x + y) := by
  simp only [Interval.Valid, add, Nat.cast_add] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mul_valid {S : ℕ} (hS : 0 < S) {a b : Interval} {x y : ℝ}
    (hx : a.Valid S x) (hy : b.Valid S y) : (mul S a b).Valid S (x * y) := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hlow := mul_le_mul hx.1 hy.1 (Nat.cast_nonneg b.lo)
    (mul_nonneg hs.le (valid_nonneg hS hx))
  have hhigh := mul_le_mul hx.2 hy.2
    (mul_nonneg hs.le (valid_nonneg hS hy)) (Nat.cast_nonneg a.hi)
  have hfloor := nat_div_lower (a.lo * b.lo) S
  have hceil := nat_div_upper (a.hi * b.hi) S hS
  push_cast at hfloor hceil
  constructor
  · change ((a.lo * b.lo / S : ℕ) : ℝ) ≤ (S : ℝ) * (x * y)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith only [hlow, hfloor]
  · change (S : ℝ) * (x * y) ≤ ((a.hi * b.hi / S + 1 : ℕ) : ℝ)
    apply (mul_le_mul_iff_left₀ hs).mp
    push_cast
    nlinarith only [hhigh, hceil]

theorem divNat_valid {S d : ℕ} (hd : 0 < d) {a : Interval} {x : ℝ}
    (hx : a.Valid S x) : (divNat d a).Valid S (x / (d : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · change ((a.lo / d : ℕ) : ℝ) ≤ (S : ℝ) * (x / (d : ℝ))
    rw [← mul_div_assoc, le_div_iff₀ hd']
    exact (nat_div_lower a.lo d).trans hx.1
  · change (S : ℝ) * (x / (d : ℝ)) ≤ ((a.hi / d + 1 : ℕ) : ℝ)
    rw [← mul_div_assoc, div_le_iff₀ hd']
    exact hx.2.trans (nat_div_upper a.hi d hd)

theorem ratio_valid {S p d : ℕ} (hd : 0 < d) :
    (ratio S p d).Valid S ((p : ℝ) / (d : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · change ((S * p / d : ℕ) : ℝ) ≤ (S : ℝ) * ((p : ℝ) / (d : ℝ))
    rw [← mul_div_assoc, le_div_iff₀ hd']
    simpa using nat_div_lower (S * p) d
  · change (S : ℝ) * ((p : ℝ) / (d : ℝ)) ≤ ((S * p / d + 1 : ℕ) : ℝ)
    rw [← mul_div_assoc, div_le_iff₀ hd']
    simpa using nat_div_upper (S * p) d hd

theorem series_valid {S : ℕ} (hS : 0 < S) {t : Interval} {x : ℝ}
    (hx : t.Valid S x) (n : ℕ) :
    (series S t n).power.Valid S (x ^ (2 * n + 1)) ∧
    (series S t n).total.Valid S
      (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
  induction n with
  | zero => simpa [series] using And.intro hx (zero_valid S)
  | succ n ih =>
      constructor
      · have h := mul_valid hS ih.1 (mul_valid hS hx hx)
        have he : x ^ (2 * n + 1) * (x * x) = x ^ (2 * (n + 1) + 1) := by ring
        simpa only [series, he] using h
      · have h := add_valid ih.2 (divNat_valid (show 0 < 2 * n + 1 by omega) ih.1)
        simpa [series, Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul] using h

/-- Soundness of the rounded integer evaluator, including its tail bound. -/
theorem logInterval_valid {S : ℕ} (hS : 0 < S) {t : Interval} {x : ℝ}
    (hx : t.Valid S x) (hsmall : x ≤ 1 / 3) (n : ℕ) :
    (logInterval S t n).Valid S (Real.log ((1 + x) / (1 - x))) := by
  have hx0 := valid_nonneg hS hx
  have hx1 : x < 1 := by linarith
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hv := series_valid hS hx n
  have hl := Real.sum_range_le_log_div hx0 hx1 n
  have hu := Real.log_div_le_sum_range_add hx0 hx1 n
  have hsq : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hden : 0 < 1 - x ^ 2 := by linarith
  have hp : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  have htail : x ^ (2 * n + 1) / (1 - x ^ 2) ≤
      (9 / 8 : ℝ) * x ^ (2 * n + 1) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hsq)]
  have htailScaled := mul_le_mul_of_nonneg_left htail hs.le
  have hloScaled := mul_le_mul_of_nonneg_left hl hs.le
  have hhiScaled := mul_le_mul_of_nonneg_left hu hs.le
  have hceil := nat_div_upper (9 * (series S t n).power.hi) 8 (by omega)
  push_cast at hceil
  constructor
  · change ((2 * (series S t n).total.lo : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith only [hv.2.1, hloScaled]
  · change _ ≤ ((2 * ((series S t n).total.hi +
      (9 * (series S t n).power.hi / 8 + 1)) : ℕ) : ℝ)
    push_cast
    nlinarith only [hv.2.2, hv.1.2, hhiScaled, htailScaled, hceil]

theorem unitLog_valid {S p d n : ℕ} (hS : 0 < S) (hd : 0 < d)
    (hlo : d ≤ p) (hhi : p ≤ 2 * d) :
    (unitLog S p d n).Valid S (Real.log ((p : ℝ) / (d : ℝ))) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp' : (0 : ℝ) < p := by exact_mod_cast (hd.trans_le hlo)
  have hsum : 0 < p + d := by omega
  have hsum' : (0 : ℝ) < (p : ℝ) + d := by positivity
  have hnorm : ((p - d : ℕ) : ℝ) / ((p + d : ℕ) : ℝ) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by exact_mod_cast hsum : (0 : ℝ) < (p + d : ℕ))]
    have hh : 3 * (p - d) ≤ p + d := by omega
    have hr : (3 : ℝ) * (p - d : ℕ) ≤ (p + d : ℕ) := by exact_mod_cast hh
    linarith
  have h := logInterval_valid hS (ratio_valid (S := S) (p := p - d) hsum) hnorm n
  have he : (1 + ((p - d : ℕ) : ℝ) / ((p + d : ℕ) : ℝ)) /
      (1 - ((p - d : ℕ) : ℝ) / ((p + d : ℕ) : ℝ)) = (p : ℝ) / d := by
    rw [Nat.cast_sub hlo, Nat.cast_add]
    field_simp [hd'.ne', hsum'.ne']
    ring
  simpa only [unitLog, he] using h

theorem scaledLog_valid {S p d k n : ℕ} (hS : 0 < S) (hp : 0 < p) (hd : 0 < d)
    (hlo : d ≤ p * 2 ^ k) (hhi : p * 2 ^ k ≤ 2 * d) :
    (scaledLog S p d k n).Valid S (Real.log ((p : ℝ) / (d : ℝ))) := by
  have ha := unitLog_valid (n := n) hS hd hlo hhi
  have hb := unitLog_valid (p := 2) (d := 1) (n := n) hS (by omega)
    (by omega) (by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq : ((p * 2 ^ k : ℕ) : ℝ) / (d : ℝ) =
      ((p : ℝ) / (d : ℝ)) * (2 : ℝ) ^ k := by push_cast; ring
  rw [hq, Real.log_mul (div_ne_zero hp'.ne' hd'.ne') (by positivity), Real.log_pow] at ha
  norm_num only [Nat.cast_ofNat, div_one] at hb
  have hl := mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg k (α := ℝ))
  have hu := mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg k (α := ℝ))
  simp only [scaledLog, SignedInterval.Valid, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  constructor
  · calc
      _ ≤ (S : ℝ) * (Real.log ((p : ℝ) / d) + (k : ℝ) * Real.log 2) -
          (k : ℝ) * ((S : ℝ) * Real.log 2) := sub_le_sub ha.1 hu
      _ = _ := by ring
  · calc
      _ = (S : ℝ) * (Real.log ((p : ℝ) / d) + (k : ℝ) * Real.log 2) -
          (k : ℝ) * ((S : ℝ) * Real.log 2) := by ring
      _ ≤ _ := sub_le_sub ha.2 hl

end MME.DyadicLog
open MME.DyadicLog

theorem solution {S p d k n : ℕ} (hS : 0 < S) (hp : 0 < p) (hd : 0 < d)
    (hlo : d ≤ p * 2 ^ k) (hhi : p * 2 ^ k ≤ 2 * d) :
    (scaledLog S p d k n).Valid S (Real.log ((p : ℝ) / (d : ℝ))) := by
  exact scaledLog_valid hS hp hd hlo hhi
