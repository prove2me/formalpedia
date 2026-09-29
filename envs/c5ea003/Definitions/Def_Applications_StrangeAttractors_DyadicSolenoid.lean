-- Prove2me | Definitions.Def_Applications_StrangeAttractors_DyadicSolenoid
-- name    : Applications_StrangeAttractors_DyadicSolenoid
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:06.04546+00:00
-- url     : https://prove2.me/theorems/b2a0cfac-6be6-480b-8b0b-8b5e0a31003a
-- title:
--   Aether Catalog definitions — Applications_StrangeAttractors_DyadicSolenoid
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.StrangeAttractors.DyadicSolenoid`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/StrangeAttractors/DyadicSolenoid.lean by skeleton subtraction
import Mathlib
/-
# Strange Attractors as Algebraic Objects — II. The Dyadic Solenoid Invariant

The **dyadic solenoid** is the inverse limit of the doubling map of the circle,

      S¹  ⟵×2—  S¹  ⟵×2—  S¹  ⟵  ⋯ .

It is the simplest "strange" attractor that is genuinely an inverse limit of
finite/1-dimensional pieces (it appears as the Smale solenoid attractor and as a
cross-section model of Lorenz-type flows).  Its first Čech cohomology is the
*direct limit* of the cohomologies of the circles under the maps induced by the
doubling map, namely

      H¹(solenoid) ≅ colim( ℤ —×2→ ℤ —×2→ ⋯ ) ≅ ℤ[1/2],

the additive group of **dyadic rationals**.  This file makes that group precise
as an `AddSubgroup ℚ` and proves the two facts that make it an honest *algebraic
invariant of chaos*:

## Main results

* `Dyadic`                  — the dyadic rationals `ℤ[1/2] ≤ ℚ`.
* `Dyadic.inv_two_pow_mem`  — every `1/2ⁿ` is dyadic.
* `Dyadic.two_divisible`    — **multiplication by `2` is surjective on `Dyadic`**:
    the doubling map is *invertible* on cohomology (the localization/colimit
    signature that no finite graph's `H¹` possesses).
* `Dyadic.not_fg`           — **`ℤ[1/2]` is not finitely generated**.  Hence the
    solenoid is not homotopy equivalent to any finite directed graph, whose first
    cohomology is always a finitely generated abelian group.  This is the precise
    sense in which the attractor is *strictly more complex* than its finite
    approximants.

This is the **cross-domain bridge** target: a topological/dynamical invariant
(Čech `H¹`) is computed and distinguished purely by abelian-group algebra.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The inverse limit of the doubling map is NOT
homotopy equivalent to any finite graph, and this can be certified algebraically
because its `H¹ = ℤ[1/2]` is not finitely generated.
Experiment (Experimenter): Modelled `ℤ[1/2]` as the subgroup of `ℚ` of elements
with a power-of-two denominator.  Proved (a) `2·_` is onto it (division by two is
internal), (b) it is not finitely generated, by trapping any finite generating
set inside a fixed `boundedDen N` (denominator dividing `2ᴺ`) and exhibiting the
escapee `1/2^{N+1}`.
Analysis (Analyst): The whole obstruction is *unbounded denominators*; finite
generation forces a uniform denominator bound, which the dyadic tower violates.
"True and moderately hard": the work is the directed-union bound on a finite set.
Critique (Critic): Not vacuous — `not_fg` is a strict negation with an explicit
witness; `two_divisible` is a genuine surjectivity statement, not `rfl`.  The
contrast with finite graphs (whose `H¹` is f.g.) is what gives it teeth.
Synthesis (PI): `ℤ[1/2]` is the certificate: chaos ⇒ non-finite-generation.
-- !-- Lab Notes -- !--
-/

namespace StrangeAttractors

open scoped Classical

/-- The dyadic rationals `ℤ[1/2]`, as the additive subgroup of `ℚ` consisting of
rationals `q` such that `2ᵏ · q` is an integer for some `k`.  This is the first
Čech cohomology group of the dyadic solenoid. -/
def Dyadic : AddSubgroup ℚ where
  carrier := {q : ℚ | ∃ (k : ℕ) (m : ℤ), (m : ℚ) = 2 ^ k * q}
  add_mem' := by
    rintro a b ⟨k₁, m₁, h₁⟩ ⟨k₂, m₂, h₂⟩
    refine ⟨k₁ + k₂, 2 ^ k₂ * m₁ + 2 ^ k₁ * m₂, ?_⟩
    push_cast
    rw [pow_add]
    have e₁ : (2 : ℚ) ^ k₂ * (m₁ : ℚ) = 2 ^ k₂ * (2 ^ k₁ * a) := by rw [h₁]
    have e₂ : (2 : ℚ) ^ k₁ * (m₂ : ℚ) = 2 ^ k₁ * (2 ^ k₂ * b) := by rw [h₂]
    rw [e₁, e₂]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨k, m, h⟩
    exact ⟨k, -m, by push_cast; rw [h]; ring⟩




/-- Auxiliary subgroup: rationals whose denominator divides `2ᴺ`, i.e. `2ᴺ · q`
is an integer.  These are the dyadics of *bounded* level. -/
def boundedDen (N : ℕ) : AddSubgroup ℚ where
  carrier := {q : ℚ | ∃ m : ℤ, (m : ℚ) = 2 ^ N * q}
  add_mem' := by
    rintro a b ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    exact ⟨m₁ + m₂, by push_cast; rw [h₁, h₂]; ring⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro a ⟨m, h⟩
    exact ⟨-m, by push_cast; rw [h]; ring⟩



/-
A finite set of dyadic rationals has a uniform denominator bound.
-/



end StrangeAttractors


