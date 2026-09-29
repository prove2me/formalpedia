-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_map
-- name    : ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand_map
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:59:46.180663+00:00
-- url     : https://prove2.me/theorems/9e7bd880-2f60-4b73-8242-1ea226a60c61
-- title:
--   Source shifted asummand map
-- statement:
--   For a ring homomorphism f:ℤ[X]→K into a field with f(X)≠0 and source indices s≤13n, j≤14n, mapping a shifted A summand equals mapping the unshifted summand times the displayed negative power of f(X).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceBClearingR12.lean#L101-L114
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
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
# Literal B coefficient and its first polynomial clearing


This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/
open Polynomial
open scoped BigOperators
open PaperR11

open ErdosProblems.Erdos1049.PaperR12

open ErdosProblems.Erdos1049.PaperR11

theorem ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand_map {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n s j : ℕ) (hs : s ≤ 13 * n) (hj : j ≤ 14 * n)
    (hx : f X ≠ 0) :
    f (sourceShiftedASummand n s j) =
      f (sourceASummand n s) * (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) := by sorry
