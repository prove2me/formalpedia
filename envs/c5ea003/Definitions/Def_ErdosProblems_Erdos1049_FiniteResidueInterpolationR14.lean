-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_FiniteResidueInterpolationR14
-- name    : ErdosProblems_Erdos1049_FiniteResidueInterpolationR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:06.742295+00:00
-- url     : https://prove2.me/theorems/2065a665-01c7-4ad2-b6d2-5ecfb415cbbe
-- title:
--   Finite simple-pole coefficient interpolation
-- statement:
--   A proper-degree numerator is reconstructed from values at inverse pole parameters, then the finite simple-pole expansion follows without assuming that expansion. The submitted module contains the source declarations poleProduct, poleProduct_eval, poleProduct_degree, poleProduct_erase_eval_ne_zero, poleResidue, among others. Source topic: Finite simple-pole coefficient interpolation.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/FiniteResidueInterpolationR14.lean#L22-L144
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Finite simple-pole interpolation, without a partial-fractions assumption

Interpolation in the pole basis and the finite simple-pole expansion.

The numerator is reconstructed from its values at the inverse pole parameters.
The only degree premise is the ordinary proper-fraction degree condition;
there is no premise asserting the partial-fraction identity. The following
source module supplies the concrete parameters and the numerator degree.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

noncomputable def poleProduct (b : ι → K) (s : Finset ι) : K[X] :=
  ∏ i ∈ s, (1 - C (b i) * X)







noncomputable def poleResidue (P : K[X]) (b : ι → K) (s : Finset ι) (i : ι) : K :=
  P.eval (b i)⁻¹ / (poleProduct b (s.erase i)).eval (b i)⁻¹

noncomputable def poleInterpolant (P : K[X]) (b : ι → K) (s : Finset ι) : K[X] :=
  ∑ i ∈ s, C (poleResidue P b s i) * poleProduct b (s.erase i)











end ErdosProblems.Erdos1049.PaperR14


