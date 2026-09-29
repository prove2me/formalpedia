-- Prove2me | solution 5 for flt5_descent_explicit
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-14T17:05:00.455299+00:00
-- url     : https://prove2.me/submissions/515904ab-eb3c-4317-bfc9-db9adf68c68a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_gcd_rs_coprime
import Theorems.Thm_flt5_rs_eq_c1
import Theorems.Thm_flt5_z_zeta5_core

-- Sketch: flt5_descent_explicit (v9)
-- Strategy: compute gcd(r,s)=1 and r*s=c1, then delegate to flt5_z_zeta5_core.
-- Children:
--   flt5_gcd_rs_coprime : gcd(r,s)=1 from gcd(r^5,s^5)=gcd(w,v)=1
--   flt5_rs_eq_c1       : r*s=c1 from (r*s)^5=r^5*s^5=w*v=c1^5
--   flt5_z_zeta5_core   : main descent theorem (algebraic number theory)

theorem solution (a b c w v c1 r s : ℤ)
    (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1)
    (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * w)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v)
    (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1)
    (hr : w = r ^ 5) (hs : v = s ^ 5) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  -- Step 1: gcd(r,s) = 1 from gcd(w,v)=gcd(r^5,s^5)=1
  have hgcd_rs : Int.gcd r s = 1 := flt5_gcd_rs_coprime r s w v hcop_wv hr hs
  -- Step 2: r*s = c1 from (r*s)^5 = r^5*s^5 = w*v = c1^5
  have hrs : r * s = c1 := flt5_rs_eq_c1 r s c1 w v hwv hr hs
  -- Step 3: Rewrite hw and hPhi with r^5, s^5
  have hw' : a + b = 5 ^ 4 * r ^ 5 := by rw [← hr]; exact hw
  have hPhi' : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5 := by
    rw [← hs]; exact hPhi
  -- Step 4: Apply flt5_z_zeta5_core (main algebraic descent)
  exact flt5_z_zeta5_core a b c r s c1 h_eq h_cop h5c hc hc1 hw' hPhi' hgcd_rs hrs
