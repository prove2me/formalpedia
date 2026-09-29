-- Prove2me | Theorems.Thm_flt5_5div_c_gcd_is_5
-- name    : flt5_5div_c_gcd_is_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:16:38.121249+00:00
-- url     : https://prove2.me/theorems/c002e615-c22e-4dd1-a0f3-d3136eeae979
-- statement:
--   Descent Case 2 for FLT n=5. If a^5+b^5=c^5, gcd(a,b)=1, and 5|c, then gcd(a+b, Phi5(a,b)) = 5. Proof: (D=gcd) D|5 by gcd_cyclotomic_dvd_5; 5|(a+b) by Fermat (since 5|c^5=a^5+b^5≡a+b mod 5); 5|Phi5 by decide on ZMod 5 (since b≡-a mod 5); so 5|D; combined with D|5: D=5.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

theorem flt5_5div_c_gcd_is_5 (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) : Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = 5 := by sorry
