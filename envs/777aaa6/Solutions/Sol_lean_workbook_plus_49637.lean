-- Prove2me | solution 1 for lean_workbook_plus_49637
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:44.764082+00:00
-- url     : https://prove2.me/submissions/57d656a2-df23-4ee9-a367-9849f802cc80

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf : StrictMono f) : ∀ n, f n ≥ n := by
  exact hf.id_le

#print axioms solution
