-- Prove2me | Theorems.Thm_flt5_coprime_wv
-- name    : flt5_coprime_wv
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T11:59:24.879307+00:00
-- url     : https://prove2.me/theorems/12e9f46f-83a3-4c5c-b096-55ca6aaf98f4
-- statement:
--   FLT-5 coprimality of descent factors. If a^5+b^5=c^5, gcd(a,b)=1, 5|c, c=5*c1, a+b=5^4*w, Phi(a,b)=5*v, and w*v=c1^5, then gcd(w,v)=1. Proof requires showing that any prime dividing both w and v leads to a contradiction with gcd(a,b)=1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_coprime_wv (a b c w v c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1) (hw : a + b = 5 ^ 4 * w) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v) (hwv : w * v = c1 ^ 5) : Int.gcd w v = 1 := by sorry
