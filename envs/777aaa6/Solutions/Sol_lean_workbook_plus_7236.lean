-- Prove2me | solution 1 for lean_workbook_plus_7236
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:10.551982+00:00
-- url     : https://prove2.me/submissions/6f8b0fd1-93af-447b-a9aa-fcab717fb979

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ a z : ℤ, 6*a+1=5*z := ⟨4, 5, by norm_num⟩
