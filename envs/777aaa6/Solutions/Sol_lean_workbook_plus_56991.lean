-- Prove2me | solution 1 for lean_workbook_plus_56991
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:42.240001+00:00
-- url     : https://prove2.me/submissions/3f372c7c-2c25-4dcb-b1b8-659953ad3fe5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem solution (p y : ℕ) (hp : p.Prime) (h : p ∣ y^2) : p ∣ y := by
  exact hp.dvd_of_dvd_pow h
