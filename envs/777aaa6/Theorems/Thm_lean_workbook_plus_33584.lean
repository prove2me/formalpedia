-- Prove2me | Theorems.Thm_lean_workbook_plus_33584
-- name    : lean_workbook_plus_33584
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a59c0200-4bc1-415b-95e0-437da02e407a
-- statement:
--   $ \zeta = \cos \frac {2\pi}{n} + i\sin \frac {2\pi}{n} = e^{\frac {2\pi i}{n}}$ , and thus ${ \{\zeta^k\}}$ are the $ n^{th}$ roots of unity, for all $ 1\leq k \leq n - 1$ , and therefore the roots of $ x^n = 1 \implies x^n - 1 = 0$ . The fundamental theorem of algebra allows us to factor it as $ x^n - 1 = (x - 1)(x - \zeta)(x - \zeta^2)...(x - \zeta^{n - 1})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33584  (n : ℕ)
  (h₀ : 0 < n) :
  ((Complex.exp (2 * π * Complex.I / n))^n - 1) = 0   :=  by sorry
