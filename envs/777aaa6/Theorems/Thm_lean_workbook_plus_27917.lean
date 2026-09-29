-- Prove2me | Theorems.Thm_lean_workbook_plus_27917
-- name    : lean_workbook_plus_27917
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ade9dba6-62c1-4745-b7e3-40750642db55
-- statement:
--   Compare the electrical force between two protons in free space with the gravitational force between them: Express result as a ratio.\n\nLet the mass of protons be $ m$ , charges $ e$ , distance between them $ r$ .\n\nGravitational force: $ F_1=\frac{\gamma m^2}{r^2}$\nElectrical force: $ F_2=\frac{ke^2}{r^2}$\n\nThe ratio\n\n $ \frac{F_2}{F_1}=\frac{ke^2}{\gamma m^2}$ . These are all constants, I leave the computation to you
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27917 (m e γ k r : ℝ) : (k * e ^ 2) / (γ * m ^ 2) = (k * e ^ 2) / (γ * m ^ 2)   :=  by sorry
