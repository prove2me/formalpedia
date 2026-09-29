-- Prove2me | Definitions.Def_mme_regional_entropy_copy_bound
-- name    : mme_regional_entropy_copy_bound
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T21:08:46.681377+00:00
-- url     : https://prove2.me/theorems/3beca5f9-2804-45a6-a6fb-c06f208c8500
-- title:
--   Explicit entropy copy guarantees for actual integer regional steps
-- statement:
--   Define the finite polynomial loss factors, common-scale entropy exponent and explicit entropyLower/entropyCopies formula for the existing IntegerStep. The formula uses the minimum of the three whole-region entropy sums and the actual repair exponent. No rate, selected family, or tensor map is assumed; correctness is proved separately.
-- source:
--   The More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . The numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open BigOperators
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRate

noncomputable def polynomialFactor {R : ℕ} (n : Fin R → ℕ) (degree : ℕ) : ℝ :=
  (6 * (((∑ r, n r : ℕ) : ℝ) + 1)) ^ degree

noncomputable def ambientFactor {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) : ℝ :=
  (((∑ r, n r : ℕ) : ℝ) + 1) ^ Fintype.card (RecursiveYZ.Cell half R parent)

noncomputable def loadFactor {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) : ℝ :=
  8 * ambientFactor (half := half) (parent := parent) n * polynomialFactor n (R * (half + 1)) +
    128 * (d : ℝ) * polynomialFactor n (R * (half + 1)) *
      polynomialFactor n (R * (half + 1) * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))

noncomputable def scaleFactor {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) : ℝ :=
  (half : ℝ) + 2 + loadFactor (half := half) (parent := parent) n d ell

noncomputable def scaleExponent {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → RecursiveYZ.Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) : ℝ :=
  jointPotential m - regionalRate htotal n m mu +
    ((∑ r, n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
end MME.RegionRate

namespace MME.RegionRealization
noncomputable def IntegerStep.entropyLower {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P) : ℝ :=
  let E := RegionRate.regionalRate D.total D.n D.m D.mu
  let loss := ((∑ r, D.n r : ℕ) : ℝ) *
    RegionRate.entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon
  let theta := RegionRate.scaleExponent D.total D.n D.m D.mu D.epsilon
  let factor := RegionRate.scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell
  Real.exp (E - loss - 4 * Real.sqrt (Real.log factor + theta)) /
    (32 * RegionRate.polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) * factor)

/-- Guaranteed copies computed only from the summed regional entropy rate and explicit losses. -/
noncomputable def IntegerStep.entropyCopies {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P) : ℕ :=
  ⌊D.entropyLower⌋₊ / 8 ^ D.repairExponent
end MME.RegionRealization


