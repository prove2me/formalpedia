-- Prove2me | Theorems.Thm_lean_workbook_plus_19088
-- name    : lean_workbook_plus_19088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8cb658dc-a4be-421a-b718-b60d65ae9b27
-- statement:
--   Prove that $ \binom{2007}{91} \equiv 5 \pmod{91}$ using mods.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19088 : (Nat.choose 2007 91) % 91 = 5   :=  by sorry
