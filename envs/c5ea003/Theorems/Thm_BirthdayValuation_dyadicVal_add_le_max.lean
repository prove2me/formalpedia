-- Prove2me | Theorems.Thm_BirthdayValuation_dyadicVal_add_le_max
-- name    : BirthdayValuation.dyadicVal_add_le_max
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:15:20.034992+00:00
-- url     : https://prove2.me/theorems/c9022368-b201-487d-90b0-2951e742ea42
-- title:
--   DyadicVal add le max
-- statement:
--   Formal statement of `BirthdayValuation.dyadicVal_add_le_max` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BirthdayValuation.dyadicVal_add_le_max(a b : ℚ) :
--       dyadicVal (a + b) ≤ max (dyadicVal a) (dyadicVal b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GameTheory/BirthdayValuationBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GameTheory/BirthdayValuationBridge.lean#L207

-- Thm stub generated from Bridges/GameTheory/BirthdayValuationBridge.lean
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

theorem BirthdayValuation.dyadicVal_add_le_max(a b : ℚ) :
    dyadicVal (a + b) ≤ max (dyadicVal a) (dyadicVal b) := by sorry
