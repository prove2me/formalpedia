-- Prove2me | solution 1 for lean_workbook_plus_59953
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:31.924268+00:00
-- url     : https://prove2.me/submissions/0bf783b4-ea7a-432a-8b02-d48642464582

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℤ) (m n : ℕ) (h1 : a ≡ b [ZMOD n]) (h2 : m ∣ n) : a ≡ b [ZMOD m] := by
  exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr h2) h1
