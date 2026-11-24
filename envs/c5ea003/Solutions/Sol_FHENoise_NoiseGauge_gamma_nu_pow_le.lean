-- Prove2me | solution 1 for FHENoise.NoiseGauge.gamma_nu_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:42.334521+00:00
-- url     : https://prove2.me/submissions/35a8ddd8-4bfd-4093-a84f-c3d9bff620c7

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R]

variable (G : NoiseGauge R)

namespace FHENoise.NoiseGauge

lemma gamma_pos : 0 < G.gamma := lt_of_lt_of_le zero_lt_one G.gamma_one_le

lemma gamma_nonneg : 0 ≤ G.gamma := le_of_lt G.gamma_pos

lemma nu_le_of_sub (x y : R) : G.nu x ≤ G.nu y + G.nu (x - y) := by
  have h : G.nu (y + (x - y)) ≤ G.nu y + G.nu (x - y) := G.nu_add_le _ _
  simpa using h

lemma gamma_nu_mul_le (x y : R) :
    G.gamma * G.nu (x * y) ≤ (G.gamma * G.nu x) * (G.gamma * G.nu y) := by
  have h := G.nu_mul_le x y
  have hg := G.gamma_nonneg
  nlinarith [G.nu_nonneg x, G.nu_nonneg y, G.gamma_pos]

lemma nu_mul_le_bounds {x y : R} {a b : ℝ} (hx : G.nu x ≤ a) (hy : G.nu y ≤ b) :
    G.nu (x * y) ≤ G.gamma * a * b := by
  have hx0 := G.nu_nonneg x
  have hy0 := G.nu_nonneg y
  have ha : 0 ≤ a := le_trans hx0 hx
  calc G.nu (x * y) ≤ G.gamma * G.nu x * G.nu y := G.nu_mul_le x y
    _ ≤ G.gamma * a * G.nu y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx G.gamma_nonneg) hy0
    _ ≤ G.gamma * a * b := mul_le_mul_of_nonneg_left hy (mul_nonneg G.gamma_nonneg ha)

end FHENoise.NoiseGauge

theorem solution (x : R) : ∀ n : ℕ, 1 ≤ n →
    G.gamma * G.nu (x ^ n) ≤ (G.gamma * G.nu x) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hik := ih hk
        have hstep : G.gamma * G.nu (x ^ k * x) ≤
            (G.gamma * G.nu (x ^ k)) * (G.gamma * G.nu x) :=
          G.gamma_nu_mul_le _ _
        have hxpos : 0 ≤ G.gamma * G.nu x :=
          mul_nonneg G.gamma_nonneg (G.nu_nonneg x)
        calc G.gamma * G.nu (x ^ (k + 1))
            = G.gamma * G.nu (x ^ k * x) := by rw [pow_succ]
          _ ≤ (G.gamma * G.nu (x ^ k)) * (G.gamma * G.nu x) := hstep
          _ ≤ (G.gamma * G.nu x) ^ k * (G.gamma * G.nu x) :=
              mul_le_mul_of_nonneg_right hik hxpos
          _ = (G.gamma * G.nu x) ^ (k + 1) := by rw [pow_succ]
