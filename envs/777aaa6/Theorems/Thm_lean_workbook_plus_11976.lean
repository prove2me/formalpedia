-- Prove2me | Theorems.Thm_lean_workbook_plus_11976
-- name    : lean_workbook_plus_11976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/934241e6-37fd-4768-bc88-2dfbe0ff5b9f
-- statement:
--   $(\overrightarrow{A}-\overrightarrow{C})^2+(\overrightarrow{B}-\overrightarrow{D})^2+(\overrightarrow{A}-\overrightarrow{D})^2+(\overrightarrow{B}-\overrightarrow{C})^2\ge (\overrightarrow{A}-\overrightarrow{B})^2 + (\overrightarrow{C}-\overrightarrow{D})^2$ $\implies \overrightarrow{A}^2+ \overrightarrow{B}^2+ \overrightarrow{C}^2+ \overrightarrow{D}^2 - 2\overrightarrow{A}\overrightarrow{C}- 2\overrightarrow{B}\overrightarrow{D}- 2\overrightarrow{A}\overrightarrow{D}- 2\overrightarrow{B}\overrightarrow{C}+ 2\overrightarrow{A}\overrightarrow{B}- 2\overrightarrow{C}\overrightarrow{D}\ge 0$ $\implies (\overrightarrow{A}+\overrightarrow{B}-\overrightarrow{C}-\overrightarrow{D})^2 \ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11976 (A B C D : ℝ) : (A - C) ^ 2 + (B - D) ^ 2 + (A - D) ^ 2 + (B - C) ^ 2 ≥ (A - B) ^ 2 + (C - D) ^ 2   :=  by sorry
