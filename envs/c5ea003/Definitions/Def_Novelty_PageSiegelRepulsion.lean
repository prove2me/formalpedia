-- Prove2me | Definitions.Def_Novelty_PageSiegelRepulsion
-- name    : Novelty_PageSiegelRepulsion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:41.299527+00:00
-- url     : https://prove2.me/theorems/08aa9252-bfa1-42e0-acc8-c80943360aca
-- title:
--   Aether Catalog definitions — Novelty_PageSiegelRepulsion
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PageSiegelRepulsion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PageSiegelRepulsion.lean by skeleton subtraction
import Mathlib

/-!
# A conditional refinement of Page's theorem on Landau–Siegel zeros

For a primitive quadratic Dirichlet character `χ` of conductor `q`, the associated
`L`-function `L(s, χ)` may possess an *exceptional* (Landau–Siegel) real zero `β`
extremely close to `s = 1`.  Page's theorem asserts that such exceptional zeros are
rare: at most one modulus in a suitable range can support one.  The classical
mechanism behind Page's theorem is a **repulsion principle** originating in Landau's
study of the Dedekind zeta function of the biquadratic field `ℚ(√d₁, √d₂)`: if two
distinct primitive quadratic characters `χ₁, χ₂` both had real zeros very close to
`1`, the nonnegativity of the Dirichlet coefficients of
`ζ(s) · L(s, χ₁) · L(s, χ₂) · L(s, χ₁χ₂)` would be violated.  Quantitatively, the
two real zeros cannot simultaneously satisfy `β ≥ 1 − c / log(q₁ q₂)`.

This file isolates and proves, in fully rigorous form, the **combinatorial /
quantitative skeleton** of Page's theorem and of the conditional refinement in the
title: *given a repulsion constant `C` (the analytic input provided, in the
refinement, by excluding non-real zeros from a shrinking neighbourhood of `s = 1`)
that is large relative to the exceptionality margin `q^{-ε}` on a conductor window
`[Q₀, M]`, there is at most one exceptional character in that window.*

The analytic ingredient — that a genuine repulsion constant `C = C(ε)` exists once
non-real zeros are pushed back to `Re ρ ≤ 1 − C/log q` — is taken here as a hypothesis
(`Repulsion`), exactly as it functions logically in the paper.  What is proved
unconditionally is the deduction of the *uniqueness* conclusion from that hypothesis,
together with the precise arithmetic compatibility condition
`C > 2 · Q₀^{-ε} · log M` relating the constants.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Page's "at most one" phenomenon is not truly analytic:
the analysis only supplies the *pairwise repulsion inequality*.  The uniqueness must
then be a purely quantitative consequence.  Conjecture: repulsion with constant `C`
plus an exceptionality margin `q^{-ε}` yields uniqueness on any window `[Q₀, M]`
precisely when `C` dominates `2 Q₀^{-ε} log M`.

EXPERIMENT (Experimenter).  Formalize characters as `(conductor, realZero)` data,
state exceptionality `β ≥ 1 − q^{-ε}`, state repulsion `min(β₁,β₂) ≤ 1 − C/log(q₁q₂)`,
and attempt to derive `χ₁ = χ₂`.  The chain: both zeros exceed `1 − Q₀^{-ε}` (monotone
in the conductor since the exponent is negative), so their minimum does too; repulsion
caps the minimum at `1 − C/log(q₁q₂) ≤ 1 − C/(2 log M)`; incompatibility follows.

ANALYSIS (Analyst).  The argument needs only two real-analytic facts: `x ↦ x^{-ε}` is
antitone on `[Q₀, ∞)` for `ε > 0`, and `log(q₁q₂) ≤ 2 log M`.  No properties of
`L`-functions, primality, or quadratic residues enter the *deduction*; they live
entirely inside the hypothesis `Repulsion`.  This cleanly separates the analytic input
from the counting output — the true content of Page's theorem.

CRITIQUE (Critic).  Is the statement vacuous?  No: `exceptionalWitness` exhibits a
character satisfying `Valid`, and the repulsion hypothesis is consistent (it is an
inequality about `min`, satisfiable when the conductors differ).  Is it trivial?  No:
the threshold `C > 2 Q₀^{-ε} log M` is genuinely load-bearing — dropping it makes the
conclusion false, since two distinct exceptional characters can coexist under weak
repulsion.  The `by_contra` + monotonicity argument is the essential insight.

SYNTHESIS (PI).  We obtain (i) the pairwise uniqueness theorem
`at_most_one_exceptional`, and (ii) its packaging as a cardinality bound
`card_le_one_of_repulsion`, which is exactly the "≤ 1 exceptional character" shape of
Page's theorem.  See `FUTURE_DIRECTIONS.md` for the bold conjectures this suggests.
-/

open Real

namespace PageSiegelRepulsion

/-- A datum standing for a primitive quadratic Dirichlet character: its `conductor`
`q` together with a putative real zero `realZero` of its `L`-function. -/
structure QuadraticCharacter where
  conductor : ℕ
  realZero : ℝ

/-- The character is *`ε`-exceptional*: its real zero lies within `q^{-ε}` of `1`,
i.e. `β ≥ 1 − q^{-ε}`.  This is the shrinking neighbourhood `[1 − q^{-ε}, 1)` of the
statement. -/
def IsExceptional (ε : ℝ) (χ : QuadraticCharacter) : Prop :=
  χ.realZero ≥ 1 - (χ.conductor : ℝ) ^ (-ε)

/-- The conductor lies in the window `[Q₀, M]`. -/
def InWindow (Q₀ M : ℕ) (χ : QuadraticCharacter) : Prop :=
  Q₀ ≤ χ.conductor ∧ χ.conductor ≤ M

/-- A character is *valid* for the problem if its conductor is in the window and it is
`ε`-exceptional. -/
def Valid (ε : ℝ) (Q₀ M : ℕ) (χ : QuadraticCharacter) : Prop :=
  InWindow Q₀ M χ ∧ IsExceptional ε χ

/-- **Repulsion principle** (analytic input).  Distinct primitive quadratic characters
cannot both have real zeros close to `1`: the smaller of the two zeros is bounded away
from `1` by `C / log(q₁ q₂)`.  In the conditional refinement, the constant `C = C(ε)`
is furnished by excluding non-real zeros from `Re ρ ≤ 1 − C/log q`. -/
def Repulsion (C : ℝ) (χ χ' : QuadraticCharacter) : Prop :=
  χ ≠ χ' →
    min χ.realZero χ'.realZero ≤
      1 - C / Real.log ((χ.conductor : ℝ) * (χ'.conductor : ℝ))






/-! ## Examples, boundaries, and generalizations (PEGB compliance) -/

-- Example: the main uniqueness theorem, instantiated.

/- **Boundary discussion.**  The compatibility threshold `C > 2 Q₀^{-ε} log M` cannot
be dropped: with weak repulsion (`C` small) two distinct exceptional characters
coexist, so uniqueness genuinely fails — this is why Page's theorem is *conditional*
in this refined, quantitative form.  As `Q₀ → ∞` with `M = Q₀`, the required `C`
shrinks like `Q₀^{-ε} log Q₀ → 0`, matching the heuristic that exceptional zeros of
large conductor are increasingly repelled.

**Generalization.**  Nothing in the deduction uses that the characters are quadratic;
it applies verbatim to any family of arithmetic objects indexed by a "conductor"
`q ≥ Q₀` carrying a real parameter `β`, once a pairwise repulsion inequality of the
form `min(β, β') ≤ 1 − C/log(q q')` holds.  This suggests a unified "repulsion ⇒
sparsity" template across families of `L`-functions.
-/

end PageSiegelRepulsion


