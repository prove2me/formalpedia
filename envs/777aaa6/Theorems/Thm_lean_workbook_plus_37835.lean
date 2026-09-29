-- Prove2me | Theorems.Thm_lean_workbook_plus_37835
-- name    : lean_workbook_plus_37835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e9a1a70f-f225-472b-b603-a8ad8374b21d
-- statement:
--   Evaluating each expression by hand, we get: $2-\sqrt{2} \approx 0.5857864376269049511983112757903019214303281246230519268233202620$ and $\sqrt{5} - 2 \approx 0.2360679774997896964091736687312762354406183596115257242708972454$ Thus $2-\sqrt{2}$ is larger.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37835 : 2 - Real.sqrt 2 > Real.sqrt 5 - 2   :=  by sorry
