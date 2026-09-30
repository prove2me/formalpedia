-- Prove2me | solution 1 for lean_workbook_plus_38388
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:38.197608+00:00
-- url     : https://prove2.me/submissions/2e4eb803-8c56-4053-aafb-058a6bf29459

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℕ) (h : 1 < Nat.gcd x y) : (Nat.gcd x y) ∣ x ∧ (Nat.gcd x y) ∣ y :=
  ⟨Nat.gcd_dvd_left x y, Nat.gcd_dvd_right x y⟩
