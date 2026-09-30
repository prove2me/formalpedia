-- Prove2me | solution 1 for lean_workbook_plus_63792
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:05.933211+00:00
-- url     : https://prove2.me/submissions/4a1e1928-a104-4a82-adcb-f0c2648a80e2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a/(b+c)+b/(c+a) ≤ 3/2 → c/(a+b) ≥ 1/6 := by
  intro h
  have hbc : 0 < b+c := add_pos hb hc
  have hca : 0 < c+a := add_pos hc ha
  have hp : 0 < a+b+2*c := by positivity
  have hid : a/(b+c)+b/(c+a)-2*(a+b)/(a+b+2*c) =
      (a-b)^2*(a+b+c)/((b+c)*(c+a)*(a+b+2*c)) := by
    field_simp [ne_of_gt hbc, ne_of_gt hca, ne_of_gt hp]
    <;> ring
  have hm : 2*(a+b)/(a+b+2*c) ≤ a/(b+c)+b/(c+a) := by
    apply sub_nonneg.mp
    rw [hid]
    positivity
  have hn := (div_le_iff₀ hp).mp (hm.trans h)
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  linarith only [hn]
