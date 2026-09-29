-- Prove2me | solution 1 for lean_workbook_plus_24996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:36.244592+00:00
-- url     : https://prove2.me/submissions/6601a35e-ffd5-4df2-84d6-e7e6b0008d80

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {X Y: Type} {f : X → Y} (g : Y → X) (h₁ : f ∘ g = id) : Function.Surjective f := by
  intros
  exact Function.RightInverse.surjective (congrFun h₁)
