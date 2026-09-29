-- Prove2me | solution 1 for lean_workbook_plus_3370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:04.544918+00:00
-- url     : https://prove2.me/submissions/f0bdb2d7-3bc8-4ee8-8e2b-1046e68b6b08

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p : ℕ) (hp : p.Prime) (h2 : p > 2) : 2 ∣ p - 1 := by
  have he := hp.even_sub_one (by omega)
  exact even_iff_two_dvd.mp he
