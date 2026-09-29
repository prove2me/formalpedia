-- Prove2me | solution 3 for flt5_descent_explicit
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T18:05:28.279071+00:00
-- url     : https://prove2.me/submissions/b6654c02-cd90-4c47-9c0e-f5a01c402ff1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt5_z_zeta5_core
import Theorems.Thm_flt5_pow5_inj

-- Sketch: flt5_descent_explicit
-- Children: flt5_z_zeta5_core + flt5_pow5_inj
-- Given w = r^5, v = s^5, reduces to flt5_z_zeta5_core with (r, s, c1).
-- Key steps: gcd(r,s)=1 from gcd(r^5,s^5)=gcd(w,v)=1
--            r*s=c1 from (r*s)^5=c1^5 via flt5_pow5_inj (injectivity of ·^5 on ℤ)

theorem solution (a b c w v c1 r s : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * w)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v)
    (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1) (hr : w = r ^ 5) (hs : v = s ^ 5) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  -- Helper: k|x → k|y → k | ↑(Int.gcd x y)
  have dvd_igcd : ∀ (k x y : ℤ), k ∣ x → k ∣ y → k ∣ ↑(Int.gcd x y) := by
    intro k x y hkx hky
    have hkx' : k.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hkx
    have hky' : k.natAbs ∣ y.natAbs := Int.natAbs_dvd_natAbs.mpr hky
    exact Int.natAbs_dvd.mp (by exact_mod_cast Nat.dvd_gcd hkx' hky')
  -- Step 1: gcd(r, s) = 1 from gcd(r^5, s^5) = gcd(w, v) = 1
  have hcop_rs : Int.gcd r s = 1 := by
    by_contra hne1
    obtain ⟨p, hp_prime, hp_dvd_gcd_rs⟩ := Nat.exists_prime_and_dvd hne1
    have hp_dvd_r : (p : ℤ) ∣ r :=
      dvd_trans (by exact_mod_cast hp_dvd_gcd_rs : (p : ℤ) ∣ ↑(Int.gcd r s))
                (Int.gcd_dvd_left r s)
    have hp_dvd_s : (p : ℤ) ∣ s :=
      dvd_trans (by exact_mod_cast hp_dvd_gcd_rs : (p : ℤ) ∣ ↑(Int.gcd r s))
                (Int.gcd_dvd_right r s)
    have hp_dvd_w : (p : ℤ) ∣ w := hr ▸ dvd_pow hp_dvd_r (by decide)
    have hp_dvd_v : (p : ℤ) ∣ v := hs ▸ dvd_pow hp_dvd_s (by decide)
    have h1 : (p : ℤ) ∣ ↑(Int.gcd w v) := dvd_igcd p w v hp_dvd_w hp_dvd_v
    rw [hcop_wv] at h1
    -- h1 : (p : ℤ) ∣ ↑1
    have hle : (p : ℤ) ≤ 1 := by
      have h1' : (p : ℤ) ∣ 1 := by exact_mod_cast h1
      exact Int.le_of_dvd (by omega) h1'
    have h2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp_prime.two_le
    omega
  -- Step 2: r * s = c1 using flt5_pow5_inj
  have hrs : r * s = c1 := by
    apply flt5_pow5_inj
    rw [mul_pow, ← hr, ← hs]
    exact hwv
  -- Step 3: Transform hypotheses
  have hw' : a + b = 5 ^ 4 * r ^ 5 := by rw [hw, hr]
  have hPhi' : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5 := by
    rw [hPhi, hs]
  exact flt5_z_zeta5_core a b c r s c1 h_eq h_cop h5c hc hc1 hw' hPhi' hcop_rs hrs
