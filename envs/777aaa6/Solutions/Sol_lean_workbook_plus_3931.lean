-- Prove2me | solution 1 for lean_workbook_plus_3931
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:46.133525+00:00
-- url     : https://prove2.me/submissions/d58f3124-1e04-4c17-9e58-5556ea25610f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (habc : 0 < a ∧ a < 1) (hbd : 0 < b ∧ b < 1) (hcd : 0 < c ∧ c < 1) (hded : 0 < d ∧ d < 1): (1-a)*(1-b)*(1-c)*(1-d) > 1-a-b-c-d := by
  have h1 : 0≤a ∧ a≤1 := ⟨habc.1.le,habc.2.le⟩
  have h2 : 0≤b ∧ b≤1 := ⟨hbd.1.le,hbd.2.le⟩
  have h3 : 0≤c ∧ c≤1 := ⟨hcd.1.le,hcd.2.le⟩
  have h4 : 0≤d ∧ d≤1 := ⟨hded.1.le,hded.2.le⟩
  have hstrict := mul_pos habc.1 hbd.1
  have ha0 := h1.1
  have hb0 := h2.1
  have hc0 := h3.1
  have hd0 := h4.1
  have hap : 0≤1-a := sub_nonneg.mpr h1.2
  have hbp : 0≤1-b := sub_nonneg.mpr h2.2
  have hcp : 0≤1-c := sub_nonneg.mpr h3.2
  have hdp : 0≤1-d := sub_nonneg.mpr h4.2
  have hab := mul_nonneg ha0 hb0
  have h1p := mul_nonneg ha0 hbp
  have habu : 0≤a+b-a*b := by nlinarith only [h1p,hb0]
  have habc := mul_nonneg hc0 habu
  have hP2 : (1-a)*(1-b)≤1 := by nlinarith only [habu]
  have hP2nn := mul_nonneg hap hbp
  have hP3 : (1-a)*(1-b)*(1-c)≤1 := by nlinarith [mul_nonneg hP2nn hc0]
  have hlast := mul_nonneg hd0 (show 0≤1-(1-a)*(1-b)*(1-c) by linarith)
  nlinarith only [hstrict,habc,hlast]
