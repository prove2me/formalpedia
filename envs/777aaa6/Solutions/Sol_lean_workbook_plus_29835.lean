-- Prove2me | solution 1 for lean_workbook_plus_29835
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:27:38.830328+00:00
-- url     : https://prove2.me/submissions/685eecad-04fd-48cf-9ee7-153d6aafe82b

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f >= 0) (x : ℝ) (hx: x >= 0) : f x >= 0 := hf x
