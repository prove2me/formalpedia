-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_rational_classification
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:58:11.205994+00:00
-- url     : https://prove2.me/submissions/598261dd-58d2-4c72-87cd-78f63e97c276

import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_rational_parameter_cleared
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_nat_classification
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_abs_reduced_positive
import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

/-!
# From an actual rational parameter to the integer scale

The numerator and denominator are obtained from the rational itself. In
particular, coprimality and positivity are proved here, not supplied as
additional assumptions on a purported parametrisation.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1) (hw : w ≠ 0)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) : m = 12 := by
  obtain ⟨hr, hs, hcop, _⟩ := rational_abs_reduced_positive w hw
  exact (cubic_scale_nat_classification m w.num.natAbs w.den hr hs hcop
    (cubic_rational_parameter_cleared m c w hm hc heq)).2.2
