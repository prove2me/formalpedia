-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
-- name    : ErdosProblems_Erdos1049_SourceOmegaCancellationR13
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:56:19.001592+00:00
-- url     : https://prove2.me/theorems/809a2729-e3bc-475a-91d2-bf81a450c497
-- title:
--   Actual all-index Omega cancellation for the literal cleared B
-- statement:
--   At primitive roots only divisible pole indices survive; the global residue-block identity cancels them and proves the literal Ω divisibility of cleared B. The submitted module contains the source declarations finite_prefix_supported_on_multiples, root_power_ne_one_of_not_dvd, sourceD_eval_zero_at_root, sourceDQuotient_eval_zero_of_not_dvd, sourceShiftedASummand_eval_eq_of_dvd, among others. Source topic: Actual all-index Omega cancellation for the literal cleared B.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceOmegaCancellationR13.lean#L21-L296
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
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
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
# Actual all-index Omega cancellation for the literal cleared B



At an ell-th primitive root only denominators with ell | j survive.
Their precise values need not be divided by an integer: the global block
identity is valid for an arbitrary function of the cutoff floor. This
avoids a spurious division at a root and also works in positive characteristic
in the finite-field stage. Descent to Z[X] uses a primitive complex root,
the cyclotomic minimal polynomial, coprimality over Q[X], and monic descent.
Distinct cyclotomic polynomials are NOT assumed comaximal over Z[X].
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators



section Field
variable {K : Type*} [Field K]









noncomputable def sourcePolePrefix (q : K) (n ell L : ℕ) : K :=
  ∑ b ∈ Icc 1 L, (sourceDQuotient n (ell * b)).eval₂ (Int.castRingHom K) q







end Field





















end ErdosProblems.Erdos1049.PaperR13


