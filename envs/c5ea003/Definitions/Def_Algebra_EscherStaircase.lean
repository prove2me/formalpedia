-- Prove2me | Definitions.Def_Algebra_EscherStaircase
-- name    : Algebra_EscherStaircase
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:14.30205+00:00
-- url     : https://prove2.me/theorems/9f06c9a2-91c2-44bd-bdf1-0963ab88333c
-- title:
--   Aether Catalog definitions — Algebra_EscherStaircase
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.EscherStaircase`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/EscherStaircase.lean by skeleton subtraction
import Mathlib

/-!
# Divisibility staircases and the ascending-chain obstruction

For an integer-valued function `f : ℤ → ℤ`, let `D n` consist of the functions
whose values are all divisible by `2^n`.  The proposed example was described as
an ascending chain.  Its containment direction is in fact the reverse:
`D (n+1) < D n`.  The chain is strictly descending and has zero intersection.

This distinction is structural.  Requiring merely that zero belong to every
ideal adds no condition at all, since every ideal contains zero.  If instead an
“Escher staircase” means an infinite strictly ascending chain, the usual
ascending-chain condition rules it out in every Noetherian ring, including
finite-variable polynomial rings and discrete valuation rings.

The results below isolate both facts: a strict divisibility filtration with
trivial intersection, and the Noetherian obstruction supplied by the usual
ascending-chain condition.  They first establish the phenomenon for all
integer-valued functions and then transfer it to the actual ring `Int(ℤ)` of
integer-valued rational polynomials.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Divisibility by increasing powers of two might produce
an infinite ascending ideal staircase, and a dimension-like height might measure
its length.  Bolder variants predicted such a staircase in every non-Noetherian
ring and assigned finite-variable polynomial rings a height equal to dimension.

Experiment (Experimenter): The containment arrows were tested directly using
constant functions.  Divisibility by `2^(n+1)` implies divisibility by `2^n`,
while the constant function `2^n` witnesses strictness.  Divisibility by every
power forces every value to vanish.

Analysis (Analyst): The advertised family is a separated descending filtration,
not an ascending chain.  Moreover, common membership of the zero polynomial is
a universal property of ideals and therefore cannot create a loop.  Krull
height concerns chains of prime ideals, whereas the proposed staircase concerns
arbitrary ideals; these are different invariants.

Critique (Critic): The polynomial-ring and discrete-valuation-ring claims were
checked against the ascending-chain condition.  Both classes are Noetherian in
the stated finite-variable setting, so neither admits an infinite strict
ascending ideal chain.  No claim about the full ring of integer-valued
polynomials is inferred from the larger function ring without an explicit
transfer argument.

Synthesis (Principal Investigator): The surviving phenomenon is reformulated as
a strict, separated divisibility filtration.  The false ascending interpretation
is replaced by a general theorem excluding infinite strict ascent in Noetherian
rings.
-- !-- Lab Notes -- !--
-/

namespace Catalog.Novelty.EscherStaircase

/-- The ideal of integer-valued functions pointwise divisible by `2^n`. -/
def divisibilityIdeal (n : ℕ) : Ideal (ℤ → ℤ) where
  carrier := {f | ∀ z, (2 : ℤ) ^ n ∣ f z}
  zero_mem' := fun _ => dvd_zero _
  add_mem' := fun hf hg z => dvd_add (hf z) (hg z)
  smul_mem' := by
    intro a f hf z
    exact dvd_mul_of_dvd_right (hf z) (a z)

/-
Increasing the exponent reverses containment of the divisibility ideals.
-/

/-
The constant function `2^n` lies on level `n`.
-/

/-
The constant function `2^n` does not lie on the next level.
-/

/-
The powers-of-two filtration is strictly descending at every step.
-/

/-
An integer divisible by every power of two is zero.
-/

/-
The intersection of all levels of the divisibility filtration is zero.
-/

/-
Membership in every level characterizes the zero function.
-/


/-
Finite-variable polynomial rings over a field admit no infinite strict
ascending chain of ideals.  Thus Krull dimension cannot be identified with the
length of such a chain.
-/

end Catalog.Novelty.EscherStaircase
namespace Catalog.Novelty.EscherStaircase

/-! ## The filtration inside the actual ring of integer-valued polynomials -/

/-- The subring of rational polynomials taking integer values at every integer. -/
def IntValuedPolynomial : Subring (Polynomial ℚ) where
  carrier := {p | ∀ z : ℤ, ∃ a : ℤ, p.eval (z : ℚ) = (a : ℚ)}
  zero_mem' := fun _ => ⟨0, by simp⟩
  one_mem' := fun _ => ⟨1, by simp⟩
  add_mem' := by
    rintro p q hp hq z
    obtain ⟨a, ha⟩ := hp z
    obtain ⟨b, hb⟩ := hq z
    exact ⟨a + b, by simp [ha, hb]⟩
  mul_mem' := by
    rintro p q hp hq z
    obtain ⟨a, ha⟩ := hp z
    obtain ⟨b, hb⟩ := hq z
    exact ⟨a * b, by simp [ha, hb]⟩
  neg_mem' := by
    rintro p hp z
    obtain ⟨a, ha⟩ := hp z
    exact ⟨-a, by simp [ha]⟩

abbrev IntZ := IntValuedPolynomial

noncomputable section

/-- The integer represented by the rational value of an integer-valued polynomial. -/
def IntZ.integerValue (p : IntZ) (z : ℤ) : ℤ := Classical.choose (p.2 z)

lemma IntZ.coe_integerValue (p : IntZ) (z : ℤ) :
    p.1.eval (z : ℚ) = (IntZ.integerValue p z : ℚ) :=
  Classical.choose_spec (p.2 z)

/-- Evaluation of an integer-valued polynomial at an integer, as a ring map to `ℤ`. -/
def IntZ.evalRingHom (z : ℤ) : IntZ →+* ℤ where
  toFun p := IntZ.integerValue p z
  map_one' := by
    apply (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℚ)))
    rw [← IntZ.coe_integerValue]
    simp
  map_zero' := by
    apply (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℚ)))
    rw [← IntZ.coe_integerValue]
    simp
  map_add' p q := by
    apply (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℚ)))
    rw [Int.cast_add, ← IntZ.coe_integerValue p z,
      ← IntZ.coe_integerValue q z, ← IntZ.coe_integerValue (p + q) z]
    simp
  map_mul' p q := by
    apply (Int.cast_injective : Function.Injective (fun x : ℤ => (x : ℚ)))
    rw [Int.cast_mul, ← IntZ.coe_integerValue p z,
      ← IntZ.coe_integerValue q z, ← IntZ.coe_integerValue (p * q) z]
    simp


/-- The ideal of integer-valued polynomials whose values are divisible by `2^n`. -/
def intZDivisibilityIdeal (n : ℕ) : Ideal IntZ :=
  ⨅ z : ℤ, Ideal.comap (IntZ.evalRingHom z) (Ideal.span {(2 : ℤ) ^ n})



/-- A constant integer, viewed as an integer-valued rational polynomial. -/
def IntZ.constant (a : ℤ) : IntZ :=
  ⟨Polynomial.C (a : ℚ), fun _ => ⟨a, by simp⟩⟩









end

end Catalog.Novelty.EscherStaircase


