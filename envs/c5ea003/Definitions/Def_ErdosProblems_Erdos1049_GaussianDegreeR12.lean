-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
-- name    : ErdosProblems_Erdos1049_GaussianDegreeR12
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:12.465781+00:00
-- url     : https://prove2.me/theorems/7fa9fddd-0158-42d0-9459-aff7c9dc94dc
-- title:
--   Exact Gaussian and actual A degrees
-- statement:
--   The Gaussian polynomial recurrence gives monicity and degree, while a unique highest A summand prevents cancellation of the literal source top coefficient. The submitted module contains the source declarations gaussian_at_one, gaussian_polynomial_symmetry, gaussian_monic_natDegree, gaussian_polynomial_monic, gaussian_polynomial_natDegree, among others. Source topic: Exact Gaussian and actual A degrees.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/GaussianDegreeR12.lean#L18-L298
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
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators



















def sourceASummandDegree (n s : ℕ) : ℕ :=
  sourceM n + sourceAExponent n s +
    12 * n * (2 * n + s) + (13 * n - s) * s











/-- The printed K is integral; natural division here is justified below. -/
def sourceK (n : ℕ) : ℕ := (1091 * n ^ 2 + 81 * n + 2) / 2















end ErdosProblems.Erdos1049.PaperR12


