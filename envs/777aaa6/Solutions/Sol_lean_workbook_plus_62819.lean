-- Prove2me | solution 1 for lean_workbook_plus_62819
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:21.387766+00:00
-- url     : https://prove2.me/submissions/8f458738-0cff-4ad4-bbb0-420a59f503c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

theorem solution (n : ℕ) (p : ℕ) (hp : p.Prime) (h : n = p^2) (d : ℕ) (hd : d = p) : d - 1 ∣ n - 1 := by
  subst h hd
  simpa using Nat.sub_dvd_pow_sub_pow d 1 2
