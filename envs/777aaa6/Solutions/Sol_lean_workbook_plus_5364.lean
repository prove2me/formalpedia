-- Prove2me | solution 1 for lean_workbook_plus_5364
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:34.408458+00:00
-- url     : https://prove2.me/submissions/a46e0959-9648-4bb8-9fe8-66f1334cfb4b

import Mathlib.Analysis.Complex.Basic

theorem solution (s : Set ℕ) (h : s.Infinite) :
    ∃ f : ℕ → ℕ, Function.Bijective f := ⟨id, Function.bijective_id⟩
