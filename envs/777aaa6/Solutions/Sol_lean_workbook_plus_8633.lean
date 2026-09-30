-- Prove2me | solution 1 for lean_workbook_plus_8633
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:25.567486+00:00
-- url     : https://prove2.me/submissions/c9b21e33-642c-4a89-aa7c-48724e5847d2

import Mathlib.Analysis.Complex.Basic

theorem solution {X : Type*} [MetricSpace X] (E : Set X) : IsClosed (closure E) :=
  isClosed_closure
