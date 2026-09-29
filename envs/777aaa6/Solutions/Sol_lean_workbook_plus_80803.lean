-- Prove2me | solution 1 for lean_workbook_plus_80803
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:58:30.000357+00:00
-- url     : https://prove2.me/submissions/fc6e1a4e-02ac-4eb5-bcae-4e9ee9572e44

import Mathlib.Tactic

theorem solution (x : ℝ) : (interior {x} = ∅) := interior_singleton x
