-- Prove2me | solution 1 for mme_CW5_base_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:59:23.754973+00:00
-- url     : https://prove2.me/submissions/b866305a-ca04-4490-926a-3de82a9ff412

import Theorems.Thm_mme_rational_log_series_certificate
import Mathlib.Tactic.FinCases

/-- The logarithms of two, five, and seven, used in the released CW-five rate,
have rational enclosures of width one trillionth. -/
theorem solution :
    let q : Fin 3 → ℚ := ![2, 5, 7]
    let lower : Fin 3 → ℚ :=
      ![693147180559 / 1000000000000, 1609437912434 / 1000000000000,
        1945910149055 / 1000000000000]
    let upper : Fin 3 → ℚ :=
      ![693147180560 / 1000000000000, 1609437912435 / 1000000000000,
        1945910149056 / 1000000000000]
    ∀ i, (lower i : ℝ) ≤ Real.log (q i : ℝ) ∧ Real.log (q i : ℝ) ≤ (upper i : ℝ) := by
  intro q lower upper i
  have hpos : ∀ i, 0 < q i := by decide +kernel
  let scale : Fin 3 → ℤ := ![-1, -2, -2]
  apply mme_rational_log_series_certificate (q i) (hpos i) (scale i) 16 (lower i) (upper i)
  all_goals fin_cases i <;> decide +kernel


#print axioms solution
