-- Prove2me | Theorems.Thm_lean_workbook_plus_78040
-- name    : lean_workbook_plus_78040
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4fae8c1e-2dbf-4b29-8eb9-024b3f14f60a
-- statement:
--   Prove that if $x \equiv y \pmod {m}$ then $Q(x) \equiv Q(y) \pmod {m}$ for any polynomial $Q(x)$ with integer coefficients.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78040 {m : ℤ} {x y : ℤ} (h : x ≡ y [ZMOD m]) (Q : Polynomial ℤ) : Q.eval x ≡ Q.eval y [ZMOD m]   :=  by sorry
