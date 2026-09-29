-- Prove2me | solution 1 for lean_workbook_plus_60842
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:07.32975+00:00
-- url     : https://prove2.me/submissions/21e1e148-7c4e-4798-b777-43cf6c883e29

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => 1 - f 0 - x) : f 0 = 1 / 2 ∧ f = fun (x:ℝ) => 1 / 2 - x := by
  have h0 := congrFun hf 0
  have hz : f 0 = 1/2 := by linarith
  refine ⟨hz,?_⟩
  funext x
  have hx := congrFun hf x
  linarith only [hx,hz]
