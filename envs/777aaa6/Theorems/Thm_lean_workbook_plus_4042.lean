-- Prove2me | Theorems.Thm_lean_workbook_plus_4042
-- name    : lean_workbook_plus_4042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/032b2782-7f43-4380-ab20-ed033f6ad671
-- statement:
--   If you chose the fair coin, the probability of getting HTHTH is $(\frac{1}{2})^5=\frac{1}{2^5}=\frac{2^5}{4^5}$ . If you choose the unfair coin, the probability of getting HTHTH is $(\frac{3}{4})^3(\frac{1}{4})^2=\frac{27}{4^5}$ . The probability that you chose the unfair die is $\frac{\frac{27}{4^5}}{\frac{27}{4^5}+\frac{2^5}{4^5}}=27/59$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4042 :
  (3 / 4)^3 * (1 / 4)^2 / (2^5 / 4^5 + 3 / 4 * (1 / 4)^2 * (3 / 4)^3) = 27 / 59   :=  by sorry
