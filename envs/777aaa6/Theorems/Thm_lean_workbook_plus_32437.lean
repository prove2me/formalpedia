-- Prove2me | Theorems.Thm_lean_workbook_plus_32437
-- name    : lean_workbook_plus_32437
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c6cc3a1a-2ee8-423c-b8e3-17fd6c6593bf
-- statement:
--   Prove or disprove the following inequalities for positive numbers a, b, and c:\n\ni) $\dfrac{{{{\left( {a - b} \right)}^4}}}{{{a^2}{b^2}}} + \dfrac{{{{\left( {b - c} \right)}^4}}}{{{b^2}{c^2}}} + \dfrac{{{{\left( {c - a} \right)}^4}}}{{{c^2}{a^2}}} \ge \dfrac{1}{2}\cdot\left[\dfrac{{{{\left( {a - b} \right)}^2}}}{{ab}} + \dfrac{{{{\left( {b - c} \right)}^2}}}{{bc}} + \dfrac{{{{\left( {c - a} \right)}^2}}}{{ca}} \right]^2.$\nii) $\dfrac{{{{\left( {a - b} \right)}^4}}}{{{a^2}{b^2}}} + \dfrac{{{{\left( {b - c} \right)}^4}}}{{{b^2}{c^2}}} + \dfrac{{{{\left( {c - a} \right)}^4}}}{{{c^2}{a^2}}} \ge \dfrac{1}{2}\cdot\left[\dfrac{{{{\left( {a - b} \right)}^2}}}{{ab}} + \dfrac{{{{\left( {b - c} \right)}^2}}}{{bc}} + \dfrac{{{{\left( {c - a} \right)}^2}}}{{ca}} \right].$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32437 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 4 / (a ^ 2 * b ^ 2) + (b - c) ^ 4 / (b ^ 2 * c ^ 2) + (c - a) ^ 4 / (c ^ 2 * a ^ 2) ≥ 1 / 2 * ((a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a)) ^ 2   :=  by sorry
