-- Prove2me | solution 1 for lean_workbook_plus_58551
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:43.704853+00:00
-- url     : https://prove2.me/submissions/22b7340e-f905-4a3d-8495-ae9cd4a139a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h2 : a / b > c / d) : a / b > (a + c) / (b + d) ∧ (a + c) / (b + d) > c / d := by
  rcases h1 with ⟨ha,hb,hc,hd⟩
  have hbd : 0<b+d := by positivity
  have hcross : c*b<a*d := (div_lt_div_iff₀ hd hb).mp h2
  constructor
  · apply (div_lt_div_iff₀ hbd hb).2
    nlinarith only [hcross]
  · apply (div_lt_div_iff₀ hd hbd).2
    nlinarith only [hcross]
