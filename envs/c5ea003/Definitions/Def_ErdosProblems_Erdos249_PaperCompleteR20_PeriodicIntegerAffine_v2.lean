-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR20_PeriodicIntegerAffine_v2
-- name    : ErdosProblems_Erdos249_PaperCompleteR20_PeriodicIntegerAffine_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T01:29:25.375669+00:00
-- url     : https://prove2.me/theorems/a63179b2-5753-44e7-9be0-7b37f1a40aa1
-- title:
--   Integer-intercept affine totient forms
-- statement:
--   Defines the natural-valued interpretation of affine forms with positive slope and integer intercept for eventual totient relations.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR20/PeriodicIntegerAffine.lean#L1-L80

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect_v2
import Definitions.Def_Erdos249257_AllBaseTotientKernel_v2
import Definitions.Def_ErdosProblems_Erdos249_ResidueClassTotientSeries
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Tactic

/-!
# Periodic freezing for integer-intercept affine forms

The paper permits arbitrary integer intercepts.  The checked r7 theorem uses
natural intercepts; shifting far enough makes every intercept nonnegative,
without changing any cross determinant or the periodic coefficients.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR20

open scoped BigOperators

/-- The natural argument of an integer-intercept affine form.  Its values
before the form becomes nonnegative are irrelevant to an eventual relation. -/
def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)




end ErdosProblems.Erdos249.PaperCompleteR20


