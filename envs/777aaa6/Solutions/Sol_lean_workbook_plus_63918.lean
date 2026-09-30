-- Prove2me | solution 1 for lean_workbook_plus_63918
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:43:28.799416+00:00
-- url     : https://prove2.me/submissions/3fb7d772-d384-4842-9960-1769a1b244c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    8 * (a * b * c * d + 1) > (a + 1) * (b + 1) * (c + 1) * (d + 1) := by
  let x := a - 1
  let y := b - 1
  let z := c - 1
  let w := d - 1
  have hx : 0 < x := sub_pos.mpr ha
  have hy : 0 < y := sub_pos.mpr hb
  have hz : 0 < z := sub_pos.mpr hc
  have hw : 0 < w := sub_pos.mpr hd
  have hcert : 0 < 7 * x * y * z * w +
      6 * (x * y * z + x * y * w + x * z * w + y * z * w) +
      4 * (x * y + x * z + x * w + y * z + y * w + z * w) := by positivity
  dsimp [x, y, z, w] at hcert
  nlinarith only [hcert]

#print axioms solution
