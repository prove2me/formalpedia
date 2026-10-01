-- Prove2me | solution 1 for ConvexOn.lt_on_Ico_of_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:18:31.027674+00:00
-- url     : https://prove2.me/submissions/d2547b67-43fa-493c-8ae4-9bc71462210d

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution {f : ℝ → ℝ} {a b t c : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (ha : f a < c) (hb : f b ≤ c)
    (hat : a ≤ t) (htb : t < b) : f t < c := by
  have hab : a < b := lt_of_le_of_lt hat htb
  let u := (b - t) / (b - a)
  let v := (t - a) / (b - a)
  have hu : 0 < u := div_pos (sub_pos.mpr htb) (sub_pos.mpr hab)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hab.le)
  have huv : u + v = 1 := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have ht : u * a + v * b = t := by dsimp [u, v]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
  have h := hf.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hu.le hv huv
  simp only [smul_eq_mul, ht] at h
  have hleft : u * f a < u * c := mul_lt_mul_of_pos_left ha hu
  have hright : v * f b ≤ v * c := mul_le_mul_of_nonneg_left hb hv
  calc
    f t ≤ u * f a + v * f b := h
    _ < u * c + v * c := add_lt_add_of_lt_of_le hleft hright
    _ = c := by rw [← add_mul, huv, one_mul]
