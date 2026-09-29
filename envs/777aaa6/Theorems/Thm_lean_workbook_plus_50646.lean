-- Prove2me | Theorems.Thm_lean_workbook_plus_50646
-- name    : lean_workbook_plus_50646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ab1ddccc-012e-47a3-8287-5db2d7236717
-- statement:
--   Before collision impulse is $m_1v_0$ , after collision $(m_1+m_2)V$ , then $m_1v_0=(m_1+m_2)V\longrightarrow V=\dfrac{m_1v_0}{m_1+m_2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50646  (m₁ m₂ v₀ V : ℝ)
  (h₀ : m₁ ≠ 0 ∧ m₂ ≠ 0)
  (h₁ : (m₁ + m₂) ≠ 0)
  (h₂ : m₁ * v₀ = (m₁ + m₂) * V) :
  V = m₁ * v₀ / (m₁ + m₂)   :=  by sorry
