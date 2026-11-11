-- Prove2me | Theorems.Thm_levy_foundations_leanlevy_triplet_conversion
-- name    : levy_foundations_leanlevy_triplet_conversion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:25:04.494214+00:00
-- url     : https://prove2.me/theorems/5cc8c3df-e098-4430-97e1-bda3d80eb1f4
-- title:
--   Convert a LeanLevy triplet and its compensated exponent to the Foundations triplet convention
-- statement:
--   The LeanLevy and Foundations triplets use drift, nonnegative Gaussian variance and a Lévy jump measure with the same mathematical exponent. Transport the Lévy-measure witness and expand their compensated integrands to prove equality, adjusting drift if the truncation conventions differ.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

open MeasureTheory ProbabilityTheory

/-- Preserve the Lévy–Khintchine exponent while translating a triplet between the LeanLevy and Foundations definitions. -/
theorem levy_foundations_leanlevy_triplet_conversion
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ U : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ,
        (↑T.drift * ↑ξ * Complex.I
          - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
          + MeasureTheory.integral T.levyMeasure
              (fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x))
          = LevyFoundations.exponent U ξ := by sorry
