-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_sourceK_gt_M
-- name    : ErdosProblems.Erdos1049.PaperR13.sourceK_gt_M
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:23:15.161288+00:00
-- url     : https://prove2.me/theorems/0eb9e56e-7f28-4577-9772-938a36d8620f
-- title:
--   Source k gt m
-- statement:
--   For n≥1, the actual source A top degree K(n) exceeds its initial monomial order M(n).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBTopDegreeR13.lean#L118-L123
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
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

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

/-!
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/
open Polynomial PaperR11 PaperR12
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR13

open ErdosProblems.Erdos1049.PaperR11
open ErdosProblems.Erdos1049.PaperR12

theorem ErdosProblems.Erdos1049.PaperR13.sourceK_gt_M (n : ℕ) (hn : 1 ≤ n) : sourceM n < sourceK n := by sorry
