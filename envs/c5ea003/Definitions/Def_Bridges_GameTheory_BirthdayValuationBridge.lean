-- Prove2me | Definitions.Def_Bridges_GameTheory_BirthdayValuationBridge
-- name    : Bridges_GameTheory_BirthdayValuationBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:00.233889+00:00
-- url     : https://prove2.me/theorems/e45744f3-90d8-4da9-8d4b-d70b5d4bf33d
-- title:
--   Aether Catalog definitions — Bridges_GameTheory_BirthdayValuationBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GameTheory.BirthdayValuationBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GameTheory/BirthdayValuationBridge.lean by skeleton subtraction
import Mathlib

/-!
# Birthday-Valuation Bridge: Surreal Birthdays Meet 2-Adic Number Theory

This file develops the **Birthday–Denomination Principle**: the 2-adic valuation
of the denominator of a dyadic rational determines its position in the surreal
birthday hierarchy. We formalize:

1. The **dyadic valuation** `ν₂(q) = padicValNat 2 q.den` on ℚ
2. The **Birthday Filtration** — a filtered ring structure on dyadic rationals
3. **Subadditivity** of the birthday valuation under addition and multiplication
4. An **ultrametric inequality** for the birthday metric
5. The **tropical-birthday bridge**: birthday filtration ↔ tropical semiring valuations

## Mathematical Overview

A dyadic rational is a rational number whose denominator is a power of 2.
The surreal birthday of such a number m/2ⁿ (in lowest terms, m odd) equals n.
This connects combinatorial game theory to p-adic number theory: the birthday
hierarchy IS the 2-adic filtration restricted to dyadic rationals.

The key insight is that this filtration has **non-Archimedean** character:
  ν₂(a + b) ≤ max(ν₂(a), ν₂(b))
which is the ultrametric inequality. Combined with the Birthday-Denomination
Principle, this says that the surreal birthday of a sum is at most the maximum
of the two birthdays.

## References

* Conway, J.H. *On Numbers and Games*, Academic Press, 1976.
* Gonshor, H. *An Introduction to the Theory of Surreal Numbers*, Cambridge, 1986.
-/

open Finset BigOperators

noncomputable section

namespace BirthdayValuation

/-! ## Part I: The Dyadic Valuation on ℚ -/

/-- The **dyadic valuation** of a rational number: the 2-adic valuation of its
denominator. This measures "how deep" in the surreal birthday hierarchy the
number sits. Integers have valuation 0; 1/2 has valuation 1; 3/8 has valuation 3. -/
def dyadicVal (q : ℚ) : ℕ := padicValNat 2 q.den





/-! ## Part II: The Birthday Filtration -/

/-- The **birthday filtration** at level `n`: all rationals with denominator dividing `2^n`.
This is a subgroup (in fact, a subring) of ℚ, and corresponds to the surreal numbers
born by day n. -/
def BirthdayFiltration (n : ℕ) : Set ℚ :=
  { q : ℚ | q.den ∣ 2 ^ n }




/-
Forward direction: membership in filtration implies bounded dyadic valuation.
-/

/-
Reverse direction for dyadic rationals: bounded valuation implies membership.
-/


/-! ## Part III: Denominator Divisibility for Dyadic Arithmetic -/

/-
Key structural lemma: the denominator of a sum divides the product of
the denominators.
-/

/-
The denominator of a product divides the product of the denominators.
-/



/-! ## Part IV: The Carry Propagation — Non-Archimedean Addition -/

/-
**Carry Propagation Theorem**: When adding dyadic rationals with denominators
dividing 2^m and 2^n, the result's denominator divides 2^(max(m,n)). This is the
non-Archimedean strengthening: birthday of sum ≤ max of birthdays (not sum).
-/

/-! ## Part V: The Birthday–Denomination Principle -/

/-
**Birthday–Denomination Principle**: For a rational with denominator 2^n,
the dyadic valuation equals n. This is the fundamental bridge between surreal
birthday arithmetic and 2-adic number theory.
-/

/-
Converse direction: if the denominator is a power of 2, then
den = 2^(dyadicVal q).
-/

/-! ## Part VI: Power-of-Two Denominator Characterization -/

/-
Every rational in the birthday filtration has a power-of-2 denominator.
-/

/-! ## Part VII: Subadditivity of the Dyadic Valuation -/

/-
**Subadditivity under addition (non-Archimedean)**: for all rationals,
the denominator valuation of a sum is at most the max of the valuations.

ν₂(den(a+b)) ≤ max(ν₂(den(a)), ν₂(den(b)))
-/

/-
**Subadditivity under multiplication**: ν₂(den(a·b)) ≤ ν₂(den(a)) + ν₂(den(b)).
-/

/-! ## Part VIII: The Birthday Distance -/

/-- The **birthday distance** between two rational numbers, measured by the
2-adic depth needed to distinguish them. -/
def birthdayDist (a b : ℚ) : ℕ := dyadicVal (a - b)




/-! ## Part IX: Growth Bounds for the Birthday Hierarchy -/

/-- The number of distinct dyadic rationals in [0,1] with denominator dividing 2^n
equals 2^n + 1. -/
def countDyadicsInUnitInterval (n : ℕ) : ℕ := 2 ^ n + 1




/-! ## Part X: The Filtered Ring Structure -/

/-- **Filtered Ring Theorem**: The birthday filtration makes the dyadic rationals
into a filtered ring: F_m · F_n ⊆ F_{m+n} and F_m + F_n ⊆ F_{max(m,n)}. -/
structure BirthdayFilteredRing where
  /-- Each level is closed under negation -/
  neg_closed : ∀ n q, q ∈ BirthdayFiltration n → -q ∈ BirthdayFiltration n
  /-- Addition respects the max filtration -/
  add_closed : ∀ m n a b, a ∈ BirthdayFiltration m → b ∈ BirthdayFiltration n →
    a + b ∈ BirthdayFiltration (max m n)
  /-- Multiplication respects the sum filtration -/
  mul_closed : ∀ m n a b, a ∈ BirthdayFiltration m → b ∈ BirthdayFiltration n →
    a * b ∈ BirthdayFiltration (m + n)
  /-- Monotonicity of levels -/
  mono : ∀ m n, m ≤ n → BirthdayFiltration m ⊆ BirthdayFiltration n


/-! ## Part XI: Complexity Measure -/

/-- The two-dimensional complexity measure: (birthday, numerator size) with
lexicographic order. The birthday measures "when" a number appears; the
numerator size measures structural complexity within that birthday level. -/
structure ComplexityPair where
  birthday : ℕ
  numeratorSize : ℕ
  deriving DecidableEq

instance : LE ComplexityPair where
  le a b := a.birthday < b.birthday ∨
    (a.birthday = b.birthday ∧ a.numeratorSize ≤ b.numeratorSize)

instance : LT ComplexityPair where
  lt a b := a.birthday < b.birthday ∨
    (a.birthday = b.birthday ∧ a.numeratorSize < b.numeratorSize)

/-- Compute the complexity of a rational number. -/
def complexity (q : ℚ) : ComplexityPair where
  birthday := dyadicVal q
  numeratorSize := q.num.natAbs

/-
**Monotonicity**: simpler denominators yield lower birthday complexity.
-/

/-! ## Part XII: Falsifiable Conjecture

**Conjecture (Multiplication Defect)**:
For dyadic rationals a, b, the defect δ(a,b) = (dyadicVal a + dyadicVal b) - dyadicVal(a·b)
equals the 2-adic valuation of the product of numerators.

**Test**: Compute for all dyadic rationals with denominator ≤ 2^4.
- a = 1/4, b = 6 = 6/1: a·b = 3/2, dyadicVal = 1, sum = 2, defect = 1.
  ν₂(1·6) = ν₂(6) = 1. ✓
- a = 1/2, b = 1/2: a·b = 1/4, dyadicVal = 2, sum = 2, defect = 0.
  ν₂(1·1) = 0. ✓
- a = 3/4, b = 2/1: a·b = 3/2, dyadicVal = 1, sum = 2, defect = 1.
  ν₂(3·2) = ν₂(6) = 1. ✓
-/



end BirthdayValuation


