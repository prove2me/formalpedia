-- Prove2me | Theorems.Thm_lean_workbook_plus_29597
-- name    : lean_workbook_plus_29597
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4b923236-a167-4b8b-87b9-45245ffe0c92
-- statement:
--   That's wrong : $ 1111^{2222}=5^{2222}$ $ =(5^6)^{370}5^2=4\pmod 7$ $ 2222^{3333}=3^{3333}$ $ =(3^6)^{555}3^3=6\pmod 7$ $ 3333^{4444}=1^{4444}=1\pmod 7$ So $ 1111^{2222} + 2222^{3333} + 3333^{4444} \equiv 4 \pmod 7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29597 :
  (1111^2222 + 2222^3333 + 3333^4444) % 7 = 4   :=  by sorry
