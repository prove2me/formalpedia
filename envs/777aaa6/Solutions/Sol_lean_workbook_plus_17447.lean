-- Prove2me | solution 1 for lean_workbook_plus_17447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:34.224342+00:00
-- url     : https://prove2.me/submissions/499d500b-dffd-4be0-9e9d-ef64e977f8b7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h1 : 0 ≤ a ∧ a ≤ 1) (h2 : 0 ≤ b ∧ b ≤ 1) (h3 : 0 ≤ c ∧ c ≤ 1) (h4 : 0 ≤ d ∧ d ≤ 1) : (1 - a) * (1 - b) * (1 - c) * (1 - d) + a + b + c + d ≥ 1 := by
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
  nlinarith only [hab,habc,hlast]
