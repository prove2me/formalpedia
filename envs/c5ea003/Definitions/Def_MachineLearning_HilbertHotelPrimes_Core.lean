-- Prove2me | Definitions.Def_MachineLearning_HilbertHotelPrimes_Core
-- name    : MachineLearning_HilbertHotelPrimes_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:39.074077+00:00
-- url     : https://prove2.me/theorems/86dd28a4-df6b-454c-bae7-de2297b9287b
-- title:
--   Aether Catalog definitions — MachineLearning_HilbertHotelPrimes_Core
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HilbertHotelPrimes.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HilbertHotelPrimes/Core.lean by skeleton subtraction
import Mathlib
/-
# Hilbert's Hotel for Primes: Permutation Stability of the Prime Sequence

We study how the sequence of prime numbers behaves under permutations of the
natural numbers. The central object is the "displacement" of a permutation —
how far each element moves — and its relationship to the asymptotic behavior
of the permuted prime sequence.

## Main Definitions
- `nthPrime`: The n-th prime number (0-indexed), using `Nat.nth Nat.Prime`
- `BoundedDisplacement`: Permutations σ : ℕ ≃ ℕ with |σ(n) - n| ≤ K for all n
- `DisplacementMetric`: A metric on permutations measuring maximum displacement
- `PrimeHotelAssignment`: The canonical assignment of primes to hotel rooms

## Main Results
- Bounded displacement permutations form a subgroup of Sym(ℕ)
- Finitely supported permutations have bounded displacement
- The nth prime is strictly monotone and grows at least linearly
- Cross-domain connection: displacement induces a tropical-algebraic structure
-/


open Nat Set Filter

noncomputable section

/-! ## The nth Prime -/

/-- The n-th prime number (0-indexed). p(0) = 2, p(1) = 3, p(2) = 5, ... -/
def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n






/-
The nth prime is at least n + 2. This follows from strict monotonicity
    and the fact that the 0th prime is 2.
-/


/-! ## Bounded Displacement Permutations -/

/-- A permutation σ : ℕ ≃ ℕ has bounded displacement K if for all n,
    the distance |σ(n) - n| ≤ K. This captures permutations that don't
    move elements "too far" from their original position. -/
def BoundedDisplacement (σ : Equiv.Perm ℕ) (K : ℕ) : Prop :=
  ∀ n : ℕ, (σ n : ℤ) - (n : ℤ) ∈ Set.Icc (-(K : ℤ)) (K : ℤ)

/-- A permutation has bounded displacement if there exists some bound K. -/
def HasBoundedDisplacement (σ : Equiv.Perm ℕ) : Prop :=
  ∃ K : ℕ, BoundedDisplacement σ K

/-- A finitely supported permutation is one that fixes all but finitely many points. -/
def FinitelySupportedPerm (σ : Equiv.Perm ℕ) : Prop :=
  Set.Finite {n : ℕ | σ n ≠ n}

/-
The identity permutation has bounded displacement 0.
-/

/-
A finitely supported permutation has bounded displacement.
-/

/-
The inverse of a bounded displacement permutation is also bounded.
-/

/-
The composition of bounded displacement permutations has bounded displacement
    with the sum of the bounds.
-/

/-! ## Prime Hotel Assignment -/


/-
The canonical hotel: room n gets the nth prime.
-/

/-! ## Permuted Hotels and Ratio Sequences -/


/-- The ratio sequence: permutedPrime(n) / nthPrime(n) as a real number. -/
def primeRatioSeq (σ : Equiv.Perm ℕ) (n : ℕ) : ℝ :=
  (nthPrime (σ n) : ℝ) / (nthPrime n : ℝ)

/-
The identity permutation gives ratio 1 everywhere.
-/

/-! ## Displacement Metric: A Tropical Connection

We define a metric on bounded-displacement permutations that has a natural
interpretation in tropical geometry: the displacement is analogous to a
tropical norm (max-plus algebra). -/

/-- The displacement of a permutation at a point, as a natural number. -/
def pointDisplacement (σ : Equiv.Perm ℕ) (n : ℕ) : ℕ :=
  Int.natAbs ((σ n : ℤ) - (n : ℤ))


/-- The displacement metric on permutations of ℕ, valued in ℝ≥0∞.
    This is the supremum of pointwise displacements, which may be infinite.
    It satisfies d(id, σ) = sup_n |σ(n) - n|.
    This is a tropical norm: in the max-plus (tropical) semiring,
    sup corresponds to tropical addition. -/
def displacementNorm (σ : Equiv.Perm ℕ) : ℕ∞ :=
  ⨆ n, (pointDisplacement σ n : ℕ∞)

/-
The identity has displacement norm 0.
-/

/-
Bounded displacement is equivalent to finite displacement norm.
-/

/-! ## Key Structural Theorem: Finitely Supported → Eventually Identity Ratio

For any permutation that moves only finitely many elements, the ratio
sequence p_{σ(n)}/p_n equals 1 for all sufficiently large n. This is
a non-trivial consequence: it doesn't just say the limit is 1, but that
the sequence is *eventually constant* at 1. -/

/-
A finitely supported permutation fixes all sufficiently large elements.
-/

/-
For finitely supported permutations, the prime ratio is eventually 1.
-/

/-! ## Prime Gap Bounds from Bounded Displacement

A key insight: for bounded displacement permutations, the ratio p_{σ(n)}/p_n
is controlled by the prime gaps near n. We prove that bounded displacement
gives bounded ratio, using the monotonicity of primes. -/

/-
For bounded displacement K, the permuted prime is between the (n-K)th
    and (n+K)th primes. This gives a "sandwich" for the ratio.
-/

/-! ## Conjecture: Density of Well-Behaved Permutations

**Falsifiable Conjecture**: The set of permutations σ for which
p_{σ(n)}/p_n → 1 is dense in the symmetric group Sym(ℕ) with the
topology of pointwise convergence.

Testable prediction: For any finite partial permutation (a bijection on
{0, ..., N-1}), there exists an extension to a full permutation of ℕ
such that p_{σ(n)}/p_n → 1.

Computational test: Take random permutations of {0, ..., 10^6 - 1},
extend by identity, and check that max |p_{σ(n)}/p_n - 1| < 0.01
for n > 1000. -/

/-- A permutation σ is "ratio-convergent" if p_{σ(n)}/p_n → 1. -/
def IsRatioConvergent (σ : Equiv.Perm ℕ) : Prop :=
  Filter.Tendsto (primeRatioSeq σ) Filter.atTop (nhds 1)

/-
**Conjecture**: Every finitely supported permutation is ratio-convergent.
    This is actually a theorem, as the ratio is eventually 1.
-/

/-! ## Adjacent Transposition Analysis

The swap (n, n+1) is the simplest non-trivial permutation. We prove
it has bounded displacement 1, giving a building block for the theory. -/

/-- The swap of adjacent elements n and n+1. -/
def adjacentSwap (n : ℕ) : Equiv.Perm ℕ := Equiv.swap n (n + 1)

/-
An adjacent swap has bounded displacement 1.
-/

/-
The number of fixed points of an adjacent swap is all but 2 elements.
-/

end


