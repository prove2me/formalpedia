-- Prove2me | solution 1 for lean_workbook_plus_76272
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:27.364394+00:00
-- url     : https://prove2.me/submissions/77c3dc5f-c3ec-4439-bb7f-735eb72d2d57

import Mathlib.Tactic

theorem solution : 12 + 1 ≡ (2 + 1) [ZMOD 5] := by decide
