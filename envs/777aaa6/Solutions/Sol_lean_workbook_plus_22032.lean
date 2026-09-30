-- Prove2me | solution 1 for lean_workbook_plus_22032
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:16.918865+00:00
-- url     : https://prove2.me/submissions/45cfd27f-754c-4246-bb81-7ea1d04c20df

import Mathlib.Analysis.Complex.Basic

theorem solution (c d : ℝ) (hc : c ≠ 0) (P Q : ℝ → ℝ) (hPQ: ∀ x, (P x, Q x) = (c * x, c * x + d)) : ∃ c' d', c' ≠ 0 ∧ ∀ x, (P x, Q x) = (c' * x, c' * x + d') :=
  ⟨c, d, hc, hPQ⟩
