-- Prove2me | Theorems.Thm_flt5_5dvd_c_then_ab
-- name    : flt5_5dvd_c_then_ab
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:10:52.575247+00:00
-- url     : https://prove2.me/theorems/da95c1c9-af8c-42a9-a515-a561bf19066f
-- statement:
--   In FLT-5: if a^5+b^5=c^5 and 5|c, then 5|(a+b). Proof: by Fermat, a≡a^5 (mod 5) and b≡b^5 (mod 5), so a+b≡a^5+b^5=c^5≡0 (mod 5).

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem flt5_5dvd_c_then_ab (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h5c : (5 : ℤ) ∣ c) : (5 : ℤ) ∣ a + b := by sorry
