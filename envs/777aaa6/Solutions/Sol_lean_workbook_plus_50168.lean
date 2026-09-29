-- Prove2me | solution 1 for lean_workbook_plus_50168
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:31:37.401789+00:00
-- url     : https://prove2.me/submissions/62972c6d-a91a-44a3-a69d-55b7b1bdd530

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : (|a| + |b| + |c| - |b + c| - |c + a| - |a + b| + |a + b + c|) * (|a| + |b| + |c| + |a + b + c|) = (|b| + |c| - |b + c|) * (|a| - |b + c| + |a + b + c|) + (|c| + |a| - |c + a|) * (|b| - |c + a| + |a + b + c|) + (|a| + |b| - |a + b|) * (|c| - |a + b| + |a + b + c|) := by
  nlinarith only [sq_abs a,sq_abs b,sq_abs c,sq_abs (b+c),sq_abs (c+a),sq_abs (a+b),sq_abs (a+b+c)]
