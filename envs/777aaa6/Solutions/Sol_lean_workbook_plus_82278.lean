-- Prove2me | solution 1 for lean_workbook_plus_82278
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:46.753934+00:00
-- url     : https://prove2.me/submissions/f1ea76f1-b938-49b0-adfd-727e2a32d969

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (f g : ℕ → ℕ)
    (hf : f 0 = 0 ∧ ∀ n, f (2 * n + 1) = 2 * f n ∧ f (2 * n) = 2 * f n + 1)
    (hg : ∀ n, g n = f (f n)) : ∀ n, g (n - g n) = 0 := by
  have hzero := (hf.2 0).2
  norm_num [hf.1] at hzero
