-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
-- name    : ErdosProblems_Erdos1049_SourceHomogeneousR12
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:48:01.59798+00:00
-- url     : https://prove2.me/theorems/988f5505-0b6b-4974-976d-875daf084685
-- title:
--   Homogeneous finite transform and monomial cancellation tools
-- statement:
--   A field identity is homogenized and pulled back through the injective fraction-field map, leaving a polynomial identity in ℤ[X] for monomial cancellation. The submitted module contains the source declarations map_gaussian, map_finitePochhammer, homogeneousPochhammer, homogeneousSourceInner, pow_mul_inverse_power, among others. Source topic: Homogeneous finite transform and monomial cancellation tools.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHomogeneousR12.lean#L18-L188
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
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
# Homogeneous finite transform and monomial cancellation tools

Homogenisation removes the need to assert
that a Laurent expression is an integral polynomial. The identity is first
proved in a field, then pulled back through the injective fraction-field map.
The final displayed identity is entirely in Z[X].
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators





/-- Homogeneous product: no inverse of the polynomial variable occurs. -/
def homogeneousPochhammer {R : Type*} [CommRing R]
    (q y : R) (h N : ℕ) : R :=
  ∏ i ∈ Finset.range N, (y - q ^ (h + i))

def homogeneousSourceInner {R : Type*} [CommRing R]
    (q y : R) (a d v : ℕ) : R :=
  ∑ s ∈ Finset.range v, (-1 : R) ^ s * q ^ s.choose 2 * y ^ (v - 1 - s) *
    gaussBinom q (v - 1) s * gaussBinom q (a + d + s - 1) (a - 1)



















end ErdosProblems.Erdos1049.PaperR12


