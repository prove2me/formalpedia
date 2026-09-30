-- Prove2me | solution 1 for lean_workbook_plus_47878
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:26:35.640213+00:00
-- url     : https://prove2.me/submissions/97c89421-3c18-430e-9e0b-0973891504e1

import Mathlib.Analysis.Complex.Basic

theorem solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ∣ q - 1) (h' : q ∣ p - 1) : p = q := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have h1 := Nat.le_of_dvd (by omega) h
  have h2 := Nat.le_of_dvd (by omega) h'
  omega
