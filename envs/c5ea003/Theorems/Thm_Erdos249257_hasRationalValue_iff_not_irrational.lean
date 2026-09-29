-- Prove2me | Theorems.Thm_Erdos249257_hasRationalValue_iff_not_irrational
-- name    : Erdos249257.hasRationalValue_iff_not_irrational
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:59:42.713749+00:00
-- url     : https://prove2.me/theorems/84206f8f-01bf-4cb8-b747-fca6789025fa
-- title:
--   Rational value is equivalent to non-irrationality
-- statement:
--   A real number has a rational value exactly when it is not irrational.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/GenericTailOrbitRigidity.lean#L50-L63
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Definitions.Def_Erdos249257_GenericTailOrbitRigidity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Generic tempered tail-orbit rigidity

This module isolates the shared binary carry trunk for the
Erdős #249/#257 problems.  For a nonnegative integer coefficient sequence
`c` satisfying `c(n) ≤ n`, write

`X_c = ∑_{n≥1} c(n) / 2^n`

and let `T_c(N)` be its scaled tail after the first `N` digits.  The main
theorem says that `X_c` is rational exactly when there is a positive integer
`v` and an integer orbit

`u(N+1) = 2*u(N) - v*c(N+1)`

whose growth is tempered by `u(N) / 2^N → 0`.  Every such orbit is rigid:
`u(N) = v*T_c(N)` for every `N`.

The tempered boundary is essential.  Positivity alone is deliberately not
used as a hypothesis and is not advertised as an equivalent criterion: a
homogeneous `2^N` parasite can be added to any orbit without changing the
recurrence.  This is a NON_CLAIM guard against the superseded positive-orbit
route; it does not assert a solution of either Erdős problem.

No novelty or priority claim is made for the theorems in this file.  They are a
formal algebra/analysis interface, not publication authority.
-/


open Filter Set

open Erdos249257

theorem Erdos249257.hasRationalValue_iff_not_irrational (x : ℝ) :
    HasRationalValue x ↔ ¬ Irrational x := by sorry
