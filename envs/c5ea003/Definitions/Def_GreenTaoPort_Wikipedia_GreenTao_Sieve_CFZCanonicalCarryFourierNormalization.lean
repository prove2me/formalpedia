-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:24:08.205569+00:00
-- url     : https://prove2.me/theorems/3c6cdede-7851-4316-959a-9fe3b604b3b8
-- title:
--   Packaged Fourier and Euler data for an arbitrary canonical carry vector
-- statement:
--   At progression length $k$, the Fourier-data structure records a positive cyclic modulus $N$, sieve level $R$, primorial parameter $w$, residue shift $b$, Boolean-selected CFZ family, an integer carry vector, and two real Fourier-frequency families. The carry vector is unrestricted in this structure.
--
--   It supplies the associated carry-adjusted integer affine family, its arithmetic-to-zeta local ratio at each prime, and the large-prime Euler correction with primes at most $w$ replaced by factors equal to one. A separate field gives the complete prime-support series for the same data. The definitions use the total conventions for infinite products and series; convergence belongs to later theorems.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryFourierNormalization.lean#L25-L71

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Fourier normalization for canonical CFZ carry vectors

The canonical divisor expansion freezes one complete integer carry vector,
rather than a divisor-dependent quotient block.  This file gives that
carry-vector model the same local-ratio, Euler-tail, factorization, and
normalized Fourier API as the older carry-block model.

All estimates are uniform in the carry vector.  In particular, no
realizability or positive-density hypothesis is imposed: vectors which do
not occur in a canonical carry cell satisfy the same pointwise arithmetic
statements.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## Packaged canonical carry-vector data -/

/-- The data determining one selected canonical carry-vector Fourier
factor.  The integer carry vector is deliberately unrestricted. -/
structure SelectedCFZCanonicalCarryFourierData (k : ℕ) where
  N : ℕ
  N_neZero : NeZero N
  R : ℕ
  w : ℕ
  b : ℕ
  e : LinearFormsExponent k
  carry : SelectedCFZFormIndex e → ℤ
  t : SelectedCFZFormIndex e → ℝ
  u : SelectedCFZFormIndex e → ℝ

namespace SelectedCFZCanonicalCarryFourierData

/-- The affine family attached directly to the packaged carry vector. -/
def carryAdjustedFamily
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) :
    SelectedCFZFormIndex d.e → AffineForm (CFZVariable k) ℤ :=
  cfzCarryAdjustedFamilyAtVector
    d.N (primorial d.w) d.b
    (fun q : SelectedCFZFormIndex d.e => q.1) d.carry

/-- The arithmetic/zeta ratio at a natural prime. -/
noncomputable def primeArithmeticToZetaLocalRatio
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    pairedFourierArithmeticToZetaLocalRatio
      d.R (p : ℕ) d.carryAdjustedFamily d.t d.u

/-- The correction over primes larger than the primorial parameter, with
all primes at most `w` masked to one. -/
noncomputable def largePrimeEulerCorrection
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) : ℂ :=
  ∏' p : Nat.Primes,
    boundedMaskedComplexPrimeLocalFactor
      d.w d.primeArithmeticToZetaLocalRatio p

/-- The complete prime-support series for the packaged carry vector. -/
noncomputable def completePrimeSupportSeries
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) : ℂ :=
  cfzCanonicalCarryCompletePrimeSupportSeries
    d.N (primorial d.w) d.b d.R
    (fun q : SelectedCFZFormIndex d.e => q.1)
    d.carry d.t d.u

end SelectedCFZCanonicalCarryFourierData

/-! ## Direct good-prime geometry -/



/-! ## Uniform prime-square control and Euler tail -/







/-! ## Exact small/large-prime factorization -/















/-! ## Exact normalized completed-Euler identities -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.largePrimeEulerCorrection.eq_1,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.mk.inj,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


