-- Prove2me | solution 1 for lean_workbook_plus_81034
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:08:35.132163+00:00
-- url     : https://prove2.me/submissions/9a140987-c6b8-4b4c-bc76-94c717e43d24

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c r : ℝ) (z1 z2 : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hr : r ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (ha' : (a:ℂ) ≠ 0) (hb' : (b:ℂ) ≠ 0) (hc' : (c:ℂ) ≠ 0) (hr' : (r:ℂ) ≠ 0) (hz1' : (z1:ℂ) ≠ 0) (hz2' : (z2:ℂ) ≠ 0) : a * z1 ^ 2 + z2 ^ 2 = r ∧ z1 * (a * z1 ^ 2 - 3 * z2 ^ 2) = b ∧ z2 * (z2 ^ 2 - 3 * a * z1 ^ 2) = c → r ^ 3 = c ^ 2 + a * b ^ 2 := by
  rintro ⟨h1, h2, h3⟩
  have key : ((r:ℂ))^3 = (c:ℂ)^2 + (a:ℂ) * (b:ℂ)^2 := by
    rw [← h1, ← h2, ← h3]; ring
  exact_mod_cast key
