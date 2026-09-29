-- Prove2me | Theorems.Thm_StrangeAttractors_inv_two_pow_not_mem_boundedDen
-- name    : StrangeAttractors.inv_two_pow_not_mem_boundedDen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:28.837238+00:00
-- url     : https://prove2.me/theorems/47673b41-512e-44e2-9e36-f74e2037d6e4
-- title:
--   The escapee: `1/2^{N+1}` has denominator `2^{N+1}` which does not divide
-- statement:
--   The escapee: `1/2^{N+1}` has denominator `2^{N+1}` which does not divide
--   `2ᴺ`, so it is not in `boundedDen N`.
--
--   ```lean
--   theorem StrangeAttractors.inv_two_pow_not_mem_boundedDen(N : ℕ) :
--       (1 / 2 ^ (N + 1) : ℚ) ∉ boundedDen N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/StrangeAttractors/DyadicSolenoid.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/StrangeAttractors/DyadicSolenoid.lean#L130

-- Thm stub generated from Applications/StrangeAttractors/DyadicSolenoid.lean
import Mathlib
import Definitions.Def_Applications_StrangeAttractors_DyadicSolenoid
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

open StrangeAttractors

open scoped Classical








/-
A finite set of dyadic rationals has a uniform denominator bound.
-/

theorem StrangeAttractors.inv_two_pow_not_mem_boundedDen(N : ℕ) :
    (1 / 2 ^ (N + 1) : ℚ) ∉ boundedDen N := by sorry
