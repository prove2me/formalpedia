-- Prove2me | Theorems.Thm_lean_workbook_plus_10735
-- name    : lean_workbook_plus_10735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b70f3bc2-5e2e-4509-8cb7-d55f4e59bc33
-- statement:
--   What is the remainder when $3^{16}$ is divided by $17$ ? What is the remainder when $9^{30}$ is divided by $31$ ? Can someone explain to me how to use Euler's on this? My friend told me that was the best way, but I'm not fond of Euler's, so if someone could please explain it to me that would be excellent.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10735 :
  (3^16) % 17 = 1 ∧ (9^30) % 31 = 1   :=  by sorry
