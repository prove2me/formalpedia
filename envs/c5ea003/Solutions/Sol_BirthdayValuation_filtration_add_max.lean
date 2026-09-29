-- Prove2me | solution 1 for BirthdayValuation.filtration_add_max
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:15.539182+00:00
-- url     : https://prove2.me/submissions/0cd2716c-f5fd-4499-8b8d-65b8c44abc96

-- Sol generated from Bridges/GameTheory/BirthdayValuationBridge.lean
import Mathlib
import Definitions.Def_Bridges_GameTheory_BirthdayValuationBridge

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

open BirthdayValuation

/-! ## Part I: The Dyadic Valuation on ℚ -/






/-! ## Part II: The Birthday Filtration -/





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





/-! ## Part IX: Growth Bounds for the Birthday Hierarchy -/





/-! ## Part X: The Filtered Ring Structure -/



/-! ## Part XI: Complexity Measure -/





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




open BirthdayValuation in
theorem solution{m n : ℕ} {a b : ℚ}
    (ha : a ∈ BirthdayFiltration m) (hb : b ∈ BirthdayFiltration n) :
    a + b ∈ BirthdayFiltration (max m n) := by
  -- Since $a$ and $b$ are in their respective filtrations, their denominators divide $2^m$ and $2^n$ respectively.
  have ha_den : a.den ∣ 2 ^ m := by
    exact ha
  have hb_den : b.den ∣ 2 ^ n := by
    exact hb;
  -- Since $a.den \mid 2^m$ and $b.den \mid 2^n$, we have $a.den \mid 2^{\max(m,n)}$ and $b.den \mid 2^{\max(m,n)}$.
  have ha_den_max : a.den ∣ 2 ^ (max m n) := by
    exact dvd_trans ha_den ( pow_dvd_pow _ ( le_max_left _ _ ) )
  have hb_den_max : b.den ∣ 2 ^ (max m n) := by
    exact dvd_trans hb_den ( pow_dvd_pow _ ( le_max_right _ _ ) );
  -- By Rat.add_def, we have that (a + b).den divides lcm(a.den, b.den).
  have h_denom_div : (a + b).den ∣ Nat.lcm a.den b.den := by
    exact Rat.add_den_dvd_lcm a b
  exact dvd_trans h_denom_div ( Nat.lcm_dvd ha_den_max hb_den_max )
