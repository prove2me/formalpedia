-- Prove2me | solution 1 for lean_workbook_plus_31771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:44.709718+00:00
-- url     : https://prove2.me/submissions/54461624-9788-45fd-915e-f2f679d9fb5e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (P : ℕ → Prop)
  (hP : P 1)
  (hP' : ∀ k, P k → P (k + 1)) :
  ∀ n, 0 < n → P n := by
  intro n hn
  exact Nat.le_induction hP (fun k _ hk => hP' k hk) n hn
