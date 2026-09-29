-- Prove2me | solution 1 for lean_workbook_plus_8500
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:12:46.804077+00:00
-- url     : https://prove2.me/submissions/725d2904-ced7-4282-8fc8-11df5b5753b5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (m n p : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) : m * (m - n) * (m - p) + n * (n - m) * (n - p) + p * (p - m) * (p - n) ≥ 0 := by
  have ord (a b c : ℝ) (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) : 0 ≤ a*(a-b)*(a-c)+b*(b-a)*(b-c)+c*(c-a)*(c-b) := by
    have h1 := mul_nonneg (sq_nonneg (a-b)) (show 0 ≤ a+b-c by linarith)
    have h2 := mul_nonneg (mul_nonneg hc (show 0 ≤ a-c by linarith)) (show 0 ≤ b-c by linarith)
    nlinarith
  rcases le_total m n with hmn | hnm
  · rcases le_total n p with hnp | hpn
    · nlinarith [ord p n m hm.le hmn hnp]
    · rcases le_total m p with hmp | hpm
      · nlinarith [ord n p m hm.le hmp hpn]
      · nlinarith [ord n m p hp.le hpm hmn]
  · rcases le_total m p with hmp | hpm
    · nlinarith [ord p m n hn.le hnm hmp]
    · rcases le_total n p with hnp | hpn
      · nlinarith [ord m p n hn.le hnp hpm]
      · nlinarith [ord m n p hp.le hpn hnm]
