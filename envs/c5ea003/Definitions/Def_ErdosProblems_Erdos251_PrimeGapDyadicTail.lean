-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
-- name    : ErdosProblems_Erdos251_PrimeGapDyadicTail
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T16:37:10.783901+00:00
-- url     : https://prove2.me/theorems/0e34a5d4-53f9-40a9-91f2-348da9e73577
-- title:
--   Dyadic prime and prime-gap terms
-- statement:
--   Defines the zero-indexed primes $p_0=2,p_1=3,\ldots$, their consecutive gaps $p_{n+1}-p_n$, and the real terms $p_n/2^{n+1}$ and $(p_{n+1}-p_n)/2^{n+1}$. These are the sequences used by the convergence, series-identity and rational-denominator theorems.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L40-L41; https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L44-L45; https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L183-L184; https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L192-L193

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped BigOperators

/-!
# Erdős #251: prime-gap dyadic tails

Finite summation by parts rewrites the prime series in terms of consecutive
prime gaps.  An elementary polynomial bound for the `n`th prime then proves
unconditional convergence of both series and the exact infinite identity.

If the prime-gap sum is rational, its scaled tails form a rational dyadic
recurrence.  Denominator arithmetic forces one positive fixed tail shift to be
eventually integral, while the factorial construction proves that the actual
prime gaps are unbounded and not eventually periodic.  These facts do not by
themselves prove irrationality: a contradiction still requires smallness, or
cofinally many adjacent small mismatches, for the same fixed shift.  Neither
unboundedness nor nonperiodicity supplies that missing estimate.
-/

namespace ErdosProblems.Erdos251

/-- Zero-based prime enumeration. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Zero-based consecutive prime gap. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n































/-! ## Infinite prime-gap reformulation -/

/-- The real term in the normalized zero-based prime series. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)



/-- The real term in the corresponding consecutive-prime-gap series. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)





/-! ### Unconditional convergence -/





























/-! ## Exact tail-shift dynamics -/









































/-! ### Denominator arithmetic and integral shifts -/















/-! ## Eventual integrality collapses under a shrinking shift -/























/-! ## Unrestricted carries need not produce periodic coefficients -/

















/-! ## Denominator normal forms for rational tail recurrences -/























/-! ## Real tail orbits -/



















/-! ## Exact rationality classification for real dyadic tail orbits -/













/-! ## Polynomial-gap countermodel to coarse prime-gap inputs -/


























end ErdosProblems.Erdos251


