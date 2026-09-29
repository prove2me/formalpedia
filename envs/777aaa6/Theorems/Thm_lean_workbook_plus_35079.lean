-- Prove2me | Theorems.Thm_lean_workbook_plus_35079
-- name    : lean_workbook_plus_35079
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/de557b64-aa6b-4dc3-a5f1-7c18dbc2a621
-- statement:
--   Multiply with $ \sin \left ( \frac{\pi}{7} \right ) \cdot \sin \left ( \frac{2\pi}{7} \right ) \cdot \sin \left ( \frac{3\pi}{7} \right )$ . And use $ \sin u \cdot \sin v = \frac{1}{2} \cos (u-v) - \frac{1}{2} \cos (u+v)$ , to obtain the equivalent statement: \n$ \cos \frac{\pi}{7} - \cos \frac{5\pi}{7} = \cos \frac{\pi}{7} - \cos \frac{3\pi}{7} + \cos \frac{2\pi}{7} - \cos \frac{4\pi}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35079 : cos (π / 7) - cos (5 * π / 7) = cos (π / 7) - cos (3 * π / 7) + cos (2 * π / 7) - cos (4 * π / 7)   :=  by sorry
