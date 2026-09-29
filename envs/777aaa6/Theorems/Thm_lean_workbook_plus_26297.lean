-- Prove2me | Theorems.Thm_lean_workbook_plus_26297
-- name    : lean_workbook_plus_26297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0e1c689e-0967-4100-840f-74ff42e642c0
-- statement:
--   This is equivalent to:\n\n$x\equiv-1\pmod3$\n$x\equiv-1\pmod4$\n$x\equiv-1\pmod5$ .\n\n$x\equiv-1\pmod{lcm(3,4,5)=60}$ .\nThe smallest positive integer that is $-1\pmod{60}$ is $\boxed{59}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26297 :
  IsLeast {x : ℕ | 0 < x ∧ x ≡ -1 [ZMOD 3] ∧ x ≡ -1 [ZMOD 4] ∧ x ≡ -1 [ZMOD 5]} 59   :=  by sorry
