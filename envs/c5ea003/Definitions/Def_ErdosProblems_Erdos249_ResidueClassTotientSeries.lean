-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_ResidueClassTotientSeries
-- name    : ErdosProblems_Erdos249_ResidueClassTotientSeries
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T01:15:50.968072+00:00
-- url     : https://prove2.me/theorems/faa9e7e1-c656-4689-a088-bc61b36368a0
-- title:
--   Residue-class totient dyadic series
-- statement:
--   Defines fixed-resolution totient residue observables and the bounded dyadic-pulse framework. The module does not prove irrationality of the unprojected binary totient series.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/ResidueClassTotientSeries.lean#L1-L80

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-!
# Erdős #249: residue-class totient series and the isolated-pulse separation

This file formalises the reusable core of the "fixed resolution" attack on

`S = ∑_{n ≥ 1} φ(n) / 2 ^ n`.

Nothing here proves that `S` is irrational.  What is proved is the exact
mechanism that makes every *fixed-resolution* projection of the totient word
irrational, together with the quantitative separation it supplies.

## Main results

* `isolated_pulse_separation` — the abstract Diophantine core.  If `a : ℕ → ℤ`
  is bounded by `C`, and `a` has a nonzero letter `t` at position `p = N+1+L`
  surrounded on both sides by a block of `L` zeros, then for every `q ≥ 1` with
  `2 ^ L > 2 * q * C` the real number `q * ∑ a n / 2 ^ n` stays at distance at
  least `q * (|t| - C / 2 ^ L) / 2 ^ p` from every integer.  Both the left and
  the right zero block are used: the right block makes the tail nonzero, the
  left block makes the tail small enough to be the distance to `ℤ`.

* `two_sided_prime_isolation` — the arithmetic supply.  For `m ≥ 2` and any `r`
  with `gcd (r+1, m) = 1` there are arbitrarily large primes `p` with
  `φ p ≡ r [MOD m]` and `m ∣ φ (p ± j)` for every `0 < j ≤ L`.  Auxiliary
  primes `ℓ_j ≡ 1 [MOD m]` are produced by Dirichlet's theorem and glued by the
  Chinese remainder theorem; `ℓ_j ∣ p ± j` forces `ℓ_j - 1 ∣ φ (p ± j)`.

* `irrational_totientObservable` — the general special-value theorem.  If an
  integer letter map `f` vanishes at the zero residue and is nonzero at some
  residue `r < m` with `gcd (r+1, m) = 1`, then `∑ f (φ n mod m) / 2 ^ n` is
  irrational.  `fixed_resolution_observable_irrational` is the `m = 2 ^ k`
  specialisation (r02 Theorem 1, forward direction), where the unit condition is
  automatic for every even `r`.

* `residue_series_irrational` — the headline consequence.  For every `m ≥ 3`
  the least-residue series `A_m = ∑_{n} (φ n mod m) / 2 ^ n` is irrational.
  (`A_1 = 0` and `A_2 = 3/4` are rational, so `m ≥ 3` is sharp.)

Not formalised here: the *converse* half of r02 Theorem 1 (rational-valued
letter maps, denominator clearing, and `∑_{r even} V_{k,r} = 1/4`), and the
bit-plane independence Corollary 4 that follows from it.

The mechanism — a bounded integer coefficient sequence with arbitrarily long
two-sided isolated nonzero digits has irrational binary value — is Erdős's 1948
Lambert-series mechanism (P. Erdős, *On arithmetical properties of Lambert
series*, J. Indian Math. Soc. **12** (1948)).  The results here are auxiliary:
they concern the reduced sequences `φ n mod m`, not `φ n` itself, and the
separation they give is of scale `2 ^ (-p)` at the pulse centre `p`, which is
far weaker than what the parent problem needs.
-/

namespace ErdosProblems.Erdos249

open Finset

/-! ## Binary values of bounded integer sequences -/

/-- The binary value `∑ a n / 2 ^ n` of an integer coefficient sequence. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n

/-- The exact tail `R_N = ∑_{j ≥ 1} a (N + j) / 2 ^ j`. -/
noncomputable def dyadicTail (a : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (a (N + 1 + j) : ℝ) / 2 ^ (j + 1)







section Dyadic

variable {a : ℕ → ℤ} {C : ℝ}



















end Dyadic

/-! ## CRT + Dirichlet: two-sided prime isolation -/











/-! ## Fixed-resolution observables of the totient word -/

/-- The coefficient sequence of a fixed-resolution observable: read the totient
word at resolution `m` and apply an integer-valued letter map `f`. -/
def totientObservableCoeff (f : ℕ → ℤ) (m n : ℕ) : ℤ := f (Nat.totient n % m)

/-- The binary value of a fixed-resolution observable of the totient word. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n





/-! ## The least-residue totient series -/

/-- `A_m = ∑_{n} (φ n mod m) / 2 ^ n`, least nonnegative residues. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n





end ErdosProblems.Erdos249


