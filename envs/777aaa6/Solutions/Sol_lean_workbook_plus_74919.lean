-- Prove2me | solution 1 for lean_workbook_plus_74919
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:05.648222+00:00
-- url     : https://prove2.me/submissions/516a25fc-2333-49d1-8cea-0ed319edd33b

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (IsConnected (Set.Icc 0 1 ×ˢ Set.Ioo 0 1)) := by
  intro h
  obtain ⟨⟨a, b⟩, hab⟩ := h.nonempty
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ioo] at hab
  omega
