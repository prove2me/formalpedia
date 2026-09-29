-- Prove2me | Definitions.Def_Erdos249257_GenericTailOrbitRigidity
-- name    : Erdos249257_GenericTailOrbitRigidity
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:23:16.160113+00:00
-- url     : https://prove2.me/theorems/f693df17-2d9b-43f8-9550-7f40fbbc1a36
-- title:
--   Predicate for rational values of a real number
-- statement:
--   This bundle defines HasRationalValue(x) as the existence of integers p and positive natural v with x=p/v. It is a predicate on a real value, not a rigidity or irrationality theorem.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/GenericTailOrbitRigidity.lean#L1-L584
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
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

namespace Erdos249257

open Filter Set





/-- A real number represented by an integer numerator and a positive natural
denominator.  This is the explicit positive-denominator form of membership in
`ℚ`; it keeps the carry multiplier visible in theorem statements. -/
def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)















/-! ## Generic finite-state non-closure

Rationality of a binary coefficient series does not make the exact tail
orbit autonomous.  The balanced pulses below all have the same dyadic value
and the same complete pre-pulse history, while their first post-pulse tails
have arbitrarily large fan-out.  Thus any exact successor interface must
carry unbounded fresh-input information unless it uses additional arithmetic
structure not present in the generic tail recurrence.
-/

























/-! ## Growing-depth affine carry cocycle

The positive replacement for an autonomous state is an input-driven affine
orbit.  At depth `L`, two carries exposed to the same forcing word differ by
exactly `2^L` times their initial difference, hence become equal modulo
`2^L`.  Long jumps therefore synchronise fixed-depth residues; the terminal
forcing suffix, not the predecessor carry, is the information that must be
encoded.
-/























/-! ## Rational control models

The controls below keep generic tail-orbit arguments honest.  The first one
transports an arbitrary bounded payload through a family whose marked binary
value is always `4/9`.  The second preserves the strongest elementary
multiplicative model (`c(n)=n`) but has an affine, hence rank-two, section
structure.  Neither theorem is an irrationality statement.
-/
























end Erdos249257


