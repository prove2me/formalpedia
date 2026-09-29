-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
-- name    : ErdosProblems_Erdos1049_SourceBClearingR12
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:02.348575+00:00
-- url     : https://prove2.me/theorems/269a33c9-ccd7-4b98-b903-9173d686d6c2
-- title:
--   Literal B coefficient and its first polynomial clearing
-- statement:
--   The literal finite B expression, including negative powers, is multiplied by its displayed denominator to obtain an integer polynomial before later monomial or cyclotomic cancellation. The submitted module contains the source declarations sourceDQuotient, source_divisors_subset, sourceDQuotient_factor, source_shift_exponent_le, sourceShiftedASummand, among others. Source topic: Literal B coefficient and its first polynomial clearing.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBClearingR12.lean#L18-L207
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Literal B coefficient and its first polynomial clearing


This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
open PaperR11

/-- The explicit complement to the divisors of j inside [1,15*n]. -/
noncomputable def sourceDQuotient (n j : ℕ) : ℤ[X] :=
  ∏ l ∈ (Finset.Icc 1 (15 * n) \ j.divisors), cyclotomic l ℤ







noncomputable def sourceShiftedASummand (n s j : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) *
    X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s)) *
    sourceGaussianProduct n s



/-- The explicit integral numerator after D clearing, before either improvement. -/
noncomputable def sourceClearedB (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1),
    ((∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j))

/-- Literal finite B expression for any scalar realisation of Z[X].
For the rational function use the canonical fraction-field map; for a real
base use Polynomial.eval₂RingHom (Int.castRingHom R) x. -/
noncomputable def sourceBValue {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n : ℕ) : K :=
  ∑ s ∈ Finset.range (13 * n + 1), f (sourceASummand n s) *
    ((∑ l ∈ Finset.Icc 1 (2 * n + s), ((f X) ^ l - 1)⁻¹) +
      ∑ j ∈ Finset.Icc 1 (14 * n),
        (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((f X) ^ j - 1)⁻¹)









noncomputable def sourceBReal (n : ℕ) (x : ℝ) : ℝ :=
  sourceBValue (Polynomial.eval₂RingHom (Int.castRingHom ℝ) x) n











end ErdosProblems.Erdos1049.PaperR12


