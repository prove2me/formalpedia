-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
-- name    : ErdosProblems_Erdos1049_SourceRootBlocksR13
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:54:42.929816+00:00
-- url     : https://prove2.me/theorems/7928a29f-14d2-4920-b842-84d4e4757d11
-- title:
--   Global residue-block cancellation at the literal source indices
-- statement:
--   Residue-block decomposition keeps the floor weight constant on nonzero local residues, so the same cancellation handles the harmonic weight in cleared B. The submitted module contains the source declarations choose_two_add_r13, root_block_digits_no_carry, root_block_digits_carry, finite_sum_rectangular_blocks, gaussianPhase, among others. Source topic: Global residue-block cancellation at the literal source indices.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceRootBlocksR13.lean#L16-L288
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
# Global residue-block cancellation at the literal source indices


A weight depending on floor((2*n+s)/ell) is constant on the nonzero
local residues. This gives cancellation for every such weight, including
the harmonic weight that occurs in the cleared B numerator.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators









section Field
variable {K : Type*} [Field K]

def gaussianPhase (q : K) (k : ℕ) : K := (-1 : K) ^ k * q ^ k.choose 2









/-- The source residue with its common monomial removed, symmetrised only
inside the valid source range. Outside that range this auxiliary term is
zero, enabling a justified rectangular extension of the finite sum. -/
def sourceRootTerm (q : K) (n s : ℕ) : K :=
  gaussianPhase q s * q ^ ((n + 1) * s) *
    gaussBinom q (14 * n + s) (12 * n) * gaussBinom q (13 * n) s

def localGaussianTerm (q : K) (w a r v h : ℕ) : K :=
  (-1 : K) ^ h * q ^ (h.choose 2 + (r + 1) * h) *
    gaussBinom q v h * gaussBinom q (w + h) a











end Field
end ErdosProblems.Erdos1049.PaperR13


