-- Prove2me | Definitions.Def_Bridges_PosetTheory_ArithmeticStatistics
-- name    : Bridges_PosetTheory_ArithmeticStatistics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:18.728532+00:00
-- url     : https://prove2.me/theorems/47d6eaa6-2497-4a35-8d97-474f0d408527
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_ArithmeticStatistics
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.ArithmeticStatistics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/ArithmeticStatistics.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Arithmetic Statistics of Graph Jacobians

This file establishes the deterministic algebraic backbone connecting
graph Jacobians (via Smith normal form invariant factors) to arithmetic
statistics in the spirit of Cohen–Lenstra heuristics.

## Mathematical Context

For a finite connected graph G, the **graph Jacobian** (also called the
critical group or sandpile group) is the finite abelian group
  Jac(G) ≅ ⊕ᵢ ℤ/dᵢℤ
where (d₁, …, dᵣ) are the Smith normal form invariant factors of a
reduced Laplacian of G. These invariant factors encode the complete
arithmetic structure of Jac(G).

The **Cohen–Lenstra heuristics** predict that for random graphs in suitable
regimes, the p-primary statistics of Jac(G) follow specific distributions.
This file proves the exact finite-n structural theorems that make such
predictions mathematically precise:

1. **Divisibility criterion** (Theorem A): q^k ∣ exp(Jac(G)) iff q^k divides
   some invariant factor.
2. **Prime-power moment identity** (Theorem B): The q^k-torsion count equals
   the product of gcd(dᵢ, q^k).
3. **Profile recovery** (Theorem C): The q-primary partition profile is
   recoverable from moment valuations via discrete differences.

## Main Definitions

* `InvariantFactorData` — Smith normal form data as a function from Fin n to ℕ
* `InvariantFactorData.exponent` — the exponent (lcm of all factors)
* `InvariantFactorData.primePowerMoment` — the q^k-torsion count
* `InvariantFactorData.qProfileCount` — the q-primary profile count
* `InvariantFactorProfile` — structure for q-primary partition data

## Cross-Domain Significance

These theorems bridge:
- **Graph theory ↔ Number theory**: Graph Jacobians are finite abelian groups
  whose arithmetic invariants obey the same algebraic laws as class groups.
- **Combinatorial probability ↔ Arithmetic statistics**: Random graph
  Laplacians produce groups whose laws match Cohen–Lenstra distributions.
- **Tropical geometry ↔ Arithmetic invariants**: The Jacobian is a
  tropical-harmonic object whose invariant factors obey number-theoretic
  statistics via the Smith normal form bridge.

## References

* Cohen, H. and Lenstra, H.W. "Heuristics on class groups" (1984)
* Clancy, J. et al. "Cohen–Lenstra for Jacobians of random graphs" (2015)
* Wood, M.M. "Sandpile groups of random graphs" (2017)
-/

open Finset BigOperators

/-! ## Core Structures -/

/-- Smith normal form invariant factor data: a sequence of positive natural numbers
representing the diagonal entries of the Smith normal form of an integer matrix.
For graph Jacobians, these are the invariant factors of the reduced Laplacian,
giving Jac(G) ≅ ⊕ᵢ ℤ/dᵢℤ. -/
structure InvariantFactorData (n : ℕ) where
  /-- The invariant factors, each a positive natural number -/
  factors : Fin n → ℕ
  /-- Each invariant factor is positive -/
  pos : ∀ i, 0 < factors i

namespace InvariantFactorData

variable {n : ℕ}

/-- The exponent of the finite abelian group ⊕ᵢ ℤ/dᵢℤ,
which is the least common multiple of all invariant factors. -/
def exponent (S : InvariantFactorData n) : ℕ :=
  (Finset.univ : Finset (Fin n)).lcm S.factors

/-- The q^k-torsion count (prime-power moment): for the direct sum of cyclic groups
ℤ/d₁ℤ × ⋯ × ℤ/dₙℤ, this is ∏ᵢ gcd(dᵢ, q^k), counting elements killed by q^k. -/
def primePowerMoment (S : InvariantFactorData n) (q k : ℕ) : ℕ :=
  ∏ i : Fin n, Nat.gcd (S.factors i) (q ^ k)

/-- The q-primary profile count at level j: the number of invariant factors
divisible by q^j. This encodes the q-primary partition type of the group. -/
def qProfileCount (S : InvariantFactorData n) (q : ℕ) (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => q ^ j ∣ S.factors i)).card

/-- An invariant factor sequence is in **divisibility order** if each factor
divides the next: d₁ | d₂ | ⋯ | dₙ. This is the standard Smith normal form
convention. -/
def isDivisibilityOrdered (S : InvariantFactorData n) : Prop :=
  ∀ i j : Fin n, i ≤ j → S.factors i ∣ S.factors j

end InvariantFactorData

/-! ## Invariant Factor Profile

A novel structure organizing the q-primary partition data of a finite abelian
group. This is the key statistical fingerprint for Cohen–Lenstra comparisons. -/


/-! ## Theorem A — Divisibility Criterion via Invariant Factors

For a finite abelian group ⊕ᵢ ℤ/dᵢℤ with exponent lcm(dᵢ), and a prime q:
  q^k ∣ lcm(dᵢ) ↔ ∃ i, q^k ∣ dᵢ

This is the fundamental arithmetic observable: the exponent is controlled
by the largest prime-power factor among all invariant factors.
-/

/-
**Theorem A (Divisibility Criterion)**: A prime power q^k divides the exponent
(lcm of invariant factors) if and only if it divides at least one invariant factor.

This is the exact arithmetic observable needed for comparing random graphs to
Cohen–Lenstra predictions: the exponent and largest invariant factor become
computable through SNF data.
-/

/-! ## Theorem B — Prime-Power Moment Identity

For a finite abelian group ⊕ᵢ ℤ/dᵢℤ, the number of elements killed by q^k is:
  M_{q,k} = ∏ᵢ gcd(dᵢ, q^k)

This is the exact finite-n analog of the moment method behind Cohen–Lenstra.
-/


/-! ## Theorem C — Profile Recovery from Moment Valuations

The q-primary profile is recoverable from the valuations of prime-power moments
via discrete differencing.
-/

/-
The q-adic valuation of gcd(d, q^k) equals min(v_q(d), k).
This is the key bridge between gcd arithmetic and valuation theory.
-/

/-
**Theorem C (Profile Recovery)**: The q-primary profile at level j
equals the discrete difference of the sum ∑ᵢ min(v_q(dᵢ), k) as k goes from j-1 to j.

Specifically, #{i : q^j ∣ dᵢ} = (∑ᵢ min(v_q(dᵢ), j)) - (∑ᵢ min(v_q(dᵢ), j-1))

This means the complete q-primary partition type is recoverable from
the sequence of prime-power moments.
-/

/-! ## Theorem D — Exponent equals last invariant factor (in divisibility order)

When invariant factors are in divisibility order (d₁ | d₂ | ⋯ | dₙ),
the exponent equals the last factor dₙ. -/

/-
**Theorem D**: When invariant factors are in divisibility order,
the exponent is the last invariant factor.

Combined with Theorem A, this gives: q^k ∣ exp(⊕ ℤ/dᵢℤ) ↔ q^k ∣ dₙ,
making the exponent directly readable from the Smith normal form.
-/

/-! ## Theorem E — gcd monotonicity and moment divisibility -/

/-
gcd(d, q^k) divides gcd(d, q^{k+1}) for all d, q, k.
-/

/-
**Theorem E (Moment Monotonicity)**: Prime-power moments are monotone
in k: M_{q,k} divides M_{q,k+1}. This reflects that higher-order torsion
subgroups contain all lower-order torsion elements.
-/

/-! ## Theorem F — Profile monotonicity -/

/-
**Theorem F (Profile Monotonicity)**: The q-profile is monotone decreasing:
#{i : q^(j+1) ∣ dᵢ} ≤ #{i : q^j ∣ dᵢ}.
This holds because q^(j+1) ∣ d implies q^j ∣ d.
-/

/-! ## Computational Examples

Verify the theory on concrete examples. -/

/-- Example: The cyclic group ℤ/6ℤ has invariant factors [6]. -/
def example_Z6 : InvariantFactorData 1 where
  factors := ![6]
  pos := by intro i; fin_cases i; norm_num

/-- Example: ℤ/2ℤ × ℤ/6ℤ has invariant factors [2, 6]. -/
def example_Z2xZ6 : InvariantFactorData 2 where
  factors := ![2, 6]
  pos := by intro i; fin_cases i <;> norm_num









/-! ## Cohen–Lenstra Connection

### Conjecture (CL-ER): Cohen–Lenstra for Erdős–Rényi Graphs

Fix a prime q and p ∈ (0,1). Let Gₙ ~ G(n,p). Then for every finite abelian
q-group A:
  lim_{n→∞} Pr(Jac(Gₙ)_(q) ≅ A) = μ_{CL,q}(A)

A weaker testable prediction using Theorem B:
  lim_{n→∞} 𝔼[M_{q,k}(Jac(Gₙ))] = 𝔼_{CL}[M_{q,k}]

The theorems proved here show that:
1. The exponent is determined by the largest prime-power invariant factor
   (Theorem A), making it a clean observable for testing.
2. The moments M_{q,k} are exact products of gcd values (Theorem B),
   making them efficiently computable for random graphs.
3. The moments determine the complete q-primary partition (Theorem C),
   so moment convergence implies distributional convergence.
-/


