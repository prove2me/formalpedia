-- Prove2me | solution 1 for lean_workbook_plus_82802
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:54:31.600649+00:00
-- url     : https://prove2.me/submissions/788be5dd-fa25-41e8-9a1f-80f6c64951a0

import Mathlib.Tactic

theorem solution (a b : ℤ) : a % b = 0 ↔ b ∣ a := Int.dvd_iff_emod_eq_zero.symm
