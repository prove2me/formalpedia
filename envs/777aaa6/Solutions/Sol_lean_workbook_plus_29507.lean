-- Prove2me | solution 1 for lean_workbook_plus_29507
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:39:34.010332+00:00
-- url     : https://prove2.me/submissions/d3bafea3-6ea3-4a20-8344-d5cc715ca2c6

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) : (∃ x, x^2 + (-2 * a^2) * x + a^4 = 0) :=
  ⟨a^2, by ring⟩
