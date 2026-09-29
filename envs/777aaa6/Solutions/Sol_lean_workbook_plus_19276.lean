-- Prove2me | solution 1 for lean_workbook_plus_19276
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:22.539031+00:00
-- url     : https://prove2.me/submissions/001a9b03-65d5-4209-9d0d-ec2bcfbc1df8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p > q) (h : p + q = 102) : 16 ≤ p - q := by
  by_contra hn
  have hp0 : 51 < p := by omega
  have hp1 : p ≤ 58 := by omega
  interval_cases p <;> norm_num at hp
  have hq0 : q = 49 := by omega
  subst q
  norm_num at hq
