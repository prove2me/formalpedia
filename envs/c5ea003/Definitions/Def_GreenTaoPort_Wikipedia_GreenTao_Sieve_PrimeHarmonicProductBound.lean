-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:20.577624+00:00
-- url     : https://prove2.me/theorems/dc8d2702-c72b-4a80-81da-78c6dc0a1e56
-- title:
--   The finite prime subtype up to a natural bound
-- statement:
--   For a natural number $R$, this construction takes the finite set of natural primes at most $R$ and retypes each member as an element of the subtype of primes. The value of each prime is unchanged, and injectivity of this retyping is supplied with the finite-set map. The resulting prime-indexed finite set is used for finite Euler products and support assignments; it is empty below the first prime.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PrimeHarmonicProductBound.lean#L248-L256

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/

/-
The two integral-test lemmas below are backported from
Mathlib/Analysis/SumIntegralComparisons.lean at
db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson, Alastair Irving
-/
section GreenTaoIntegralTestCompatibility

open Set MeasureTheory MeasureSpace intervalIntegral
open scoped BigOperators

variable {f : ℝ → ℝ}





end GreenTaoIntegralTestCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter Set
open scoped BigOperators Topology

















/-- The primes at most `R`, retyped as elements of `Nat.Primes`. -/
noncomputable def primesLEAsPrimes (R : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE R).attach.map
    { toFun := fun p =>
        ⟨p.1, Nat.prime_of_mem_primesLE p.2⟩
      inj' := by
        intro p q h
        apply Subtype.ext
        exact congrArg (fun z : Nat.Primes => (z : ℕ)) h }



















end Wikipedia.SzemeredisTheorem


