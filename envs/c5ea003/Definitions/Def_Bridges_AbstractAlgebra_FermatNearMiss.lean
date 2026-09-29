-- Prove2me | Definitions.Def_Bridges_AbstractAlgebra_FermatNearMiss
-- name    : Bridges_AbstractAlgebra_FermatNearMiss
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:46.613777+00:00
-- url     : https://prove2.me/theorems/697081c3-f8dc-4ff4-b385-bcc5caed1ffc
-- title:
--   Aether Catalog definitions — Bridges_AbstractAlgebra_FermatNearMiss
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AbstractAlgebra.FermatNearMiss`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AbstractAlgebra/FermatNearMiss.lean by skeleton subtraction
import Mathlib
/-
  # Foundational Theory of Fermat Near-Misses

  This module develops the theory of Fermat near-misses: triples (a, b, c)
  where |aⁿ + bⁿ − cⁿ| is small relative to cⁿ. The key results are:

  1. **Mixed-term decomposition**: The Fermat defect of "sum triples"
     (a, b, a+b) is entirely controlled by binomial cross-terms.

  2. **Cross-term superadditivity**: For n ≥ 2 and positive a, b,
     we have aⁿ + bⁿ < (a+b)ⁿ — creating a one-sided barrier.

  3. **Power gap sandwich**: n·cⁿ⁻¹ ≤ (c+1)ⁿ − cⁿ ≤ n·(c+1)ⁿ⁻¹,
     tightly bounding consecutive power differences.

  4. **Near-miss quality measure**: A normalized measure of how close
     a triple comes to satisfying Fermat's equation.
-/

open Finset BigOperators Nat

/-! ## Core Definitions -/

/-- The Fermat defect of a triple (a, b, c) at exponent n is aⁿ + bⁿ − cⁿ.
    When this is zero, (a, b, c) satisfies Fermat's equation. -/
def fermatDefect (a b c : ℤ) (n : ℕ) : ℤ := a ^ n + b ^ n - c ^ n

 -- |defect| / c^n as a rational approximation


/-! ## The Mixed-Term Decomposition

The binomial theorem gives (a + b)ⁿ = aⁿ + bⁿ + cross-terms.
This means the Fermat defect of a sum triple (a, b, a+b) equals
minus the cross-term sum. -/

/-
**Mixed-Term Decomposition (Integer version)**:
    (a + b)ⁿ = aⁿ + bⁿ + Σ_{k=1}^{n-1} C(n,k) aᵏ bⁿ⁻ᵏ in ℤ.
    Equivalently, the Fermat defect of (a, b, a+b) is the negative
    of the binomial cross-term sum.
-/

/-! ## Cross-Term Superadditivity

For n ≥ 2, the function x ↦ xⁿ is strictly superadditive on positive reals
(and positive naturals), meaning aⁿ + bⁿ < (a+b)ⁿ. -/

/-
**Superadditivity of Powers**: For n ≥ 2 and positive a, b,
    aⁿ + bⁿ < (a + b)ⁿ. This is the fundamental one-sided barrier
    for Fermat near-misses of sum triples.
-/

/-
Sum-triple defect is always negative: for positive a, b and n ≥ 2,
    aⁿ + bⁿ − (a+b)ⁿ < 0.
-/

/-! ## Power Gap Sandwich Theorem

The difference (c+1)ⁿ − cⁿ is tightly sandwiched between
n·cⁿ⁻¹ and n·(c+1)ⁿ⁻¹. This governs the spacing of perfect
powers and hence the possible values of Fermat defects. -/

/-
**Power Gap Lower Bound**: n · cⁿ⁻¹ ≤ (c+1)ⁿ − cⁿ.
    This follows from the binomial expansion: (c+1)ⁿ − cⁿ = Σ_{k=0}^{n-1} C(n,k)cᵏ ≥ n·cⁿ⁻¹.
-/

/-
**Power Gap Upper Bound**: (c+1)ⁿ − cⁿ ≤ n · (c+1)ⁿ⁻¹.
    This follows because C(n,k) ≤ n · C(n-1,k) for k ≤ n-1,
    so the binomial expansion of (c+1)ⁿ − cⁿ is termwise bounded
    by n times the expansion of (c+1)ⁿ⁻¹.
-/


/-! ## Defect Monotonicity

As c increases past (a^n + b^n)^{1/n}, the defect a^n + b^n - c^n
becomes more negative. This means there is at most one "closest"
integer c for any given (a, b, n). -/

/-
The integer Fermat defect is strictly decreasing in c (for positive c and n ≥ 1).
-/

/-! ## Optimal Approximant Uniqueness

For any (a, b, n) with n ≥ 1, the sign change of the defect occurs within
a window of width at most 2. -/

/-
For a, b and n ≥ 1, if the defect at c₁ is ≤ 0 and at c₂ is ≥ 0,
    with c₁ ≤ c₂, then c₂ ≤ c₁ + 1. That is, the sign change happens
    between consecutive integers.
-/

/-! ## Conjecture: Near-Miss Exponent Gap

**Falsifiable Conjecture**: For n ≥ 3 and coprime positive integers a, b, c,
|aⁿ + bⁿ − cⁿ| ≥ c^{n-2}.

This is testable: compute the ratio |aⁿ + bⁿ − cⁿ| / c^{n-2} for all
coprime triples with small c. If any ratio < 1, the conjecture fails.

Note: For n = 3, this would say |a³ + b³ − c³| ≥ c, which is related to
(but weaker than) effective forms of the ABC conjecture. -/


