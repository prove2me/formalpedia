-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceComplement_monic_degree
-- name    : ErdosProblems.Erdos1049.PaperR12.sourceComplement_monic_degree
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:23:12.883934+00:00
-- url     : https://prove2.me/theorems/0a1dfb67-6ede-44be-8e67-2c338c504c4c
-- title:
--   Source complement monic degree
-- statement:
--   For every n, the complementary cyclotomic product is monic, and its degree is the sum of φ(l) over 1≤l≤15n with sourceWeight(n,l)=0.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/GaussianDegreeR12.lean#L265-L286
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
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

/-!
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
-/
open Polynomial
open PaperR11
open scoped BigOperators

open ErdosProblems.Erdos1049.PaperR12

open ErdosProblems.Erdos1049.PaperR11

theorem ErdosProblems.Erdos1049.PaperR12.sourceComplement_monic_degree (n : ℕ) :
    (sourceComplement n).Monic ∧ (sourceComplement n).natDegree =
      ∑ l ∈ Finset.Icc 1 (15 * n), if sourceWeight n l = 0 then l.totient else 0 := by sorry
