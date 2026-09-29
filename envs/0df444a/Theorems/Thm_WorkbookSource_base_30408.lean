-- Prove2me | Theorems.Thm_WorkbookSource_base_30408
-- name    : WorkbookSource.base_30408
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:18:52.966067+00:00
-- url     : https://prove2.me/theorems/91178994-0b17-407d-aa05-3bc5297bc378
-- title:
--   A shifted quadratic ratio upper bound at fixed sum three
-- statement:
--   For $a, b, c \in \mathbb{R}_{>0}$ such that $a + b + c = 3$, prove that $\dfrac{a}{a^2+2} + \dfrac{b}{b^2+2} + \dfrac{c}{c^2+2} \le 1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30408` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30408; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30408 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (a^2 + 2) + b / (b^2 + 2) + c / (c^2 + 2) ≤ 1  :=  by sorry
