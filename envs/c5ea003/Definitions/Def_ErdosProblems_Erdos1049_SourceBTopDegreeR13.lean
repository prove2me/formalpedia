-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
-- name    : ErdosProblems_Erdos1049_SourceBTopDegreeR13
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:50:41.670986+00:00
-- url     : https://prove2.me/theorems/00c3478b-56a2-4a2b-b4a6-ae245ac8dccb
-- title:
--   Exact top degree of the literal cleared B numerator
-- statement:
--   The unique unshifted (s,l)=(13n,1) term fixes the leading coefficient and exact degree of the literal cleared B polynomial; quotient construction remains separate from remainder vanishing. The submitted module contains the source declarations monic_finset_product, monic_finset_product_natDegree, sourceD_monic, sourceOmega_monic, sourceDQuotient_monic, among others. Source topic: Exact top degree of the literal cleared B numerator.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBTopDegreeR13.lean#L20-L330
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
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
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators



























/-- Natural subtraction is justified by the positive leading index below. -/
noncomputable def sourceClearedBTop (n : ℕ) : ℕ := (sourceD n).natDegree + sourceK n - 1



















/-- An actual integer polynomial, not an existential source package.
Its equality to the normalised rational B still requires its remainder to be zero. -/
noncomputable def sourceV (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n /ₘ sourceOmega n

noncomputable def sourceOmegaRemainder (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n %ₘ sourceOmega n









end ErdosProblems.Erdos1049.PaperR13


