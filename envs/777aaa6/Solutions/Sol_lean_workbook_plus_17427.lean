-- Prove2me | solution 1 for lean_workbook_plus_17427
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:14:47.857633+00:00
-- url     : https://prove2.me/submissions/91b0d24b-41e8-4efb-87f6-2b963761c3fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a / (b + c) + b / (a + c) + c / (a + b) < 2 := by
  have bound (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : u < v+w) : u/(v+w) < 2*u/(u+v+w) := by
    apply (div_lt_div_iff₀ (show 0 < v+w by linarith) (show 0 < u+v+w by linarith)).2
    have hp := mul_pos hu (show 0 < v+w-u by linarith)
    nlinarith
  have h1 := bound a b c hx.1 hx.2.1 hx.2.2 hbc
  have h2 : b/(a+c) < 2*b/(a+b+c) := by
    convert bound b a c hx.2.1 hx.1 hx.2.2 hca using 1 <;> ring
  have h3 : c/(a+b) < 2*c/(a+b+c) := by
    convert bound c a b hx.2.2 hx.1 hx.2.1 hab using 1 <;> ring
  have hs : 0 < a+b+c := by linarith [hx.1, hx.2.1, hx.2.2]
  have he : 2*a/(a+b+c)+2*b/(a+b+c)+2*c/(a+b+c) = 2 := by
    field_simp [ne_of_gt hs]
    <;> ring
  linarith
