-- Prove2me | Theorems.Thm_PageSiegelRepulsion_at_most_one_exceptional
-- name    : PageSiegelRepulsion.at_most_one_exceptional
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:19:29.885928+00:00
-- url     : https://prove2.me/theorems/5914d344-3b2f-4caa-a3c8-7a23f45eddf0
-- title:
--   Main theorem (conditional refinement of Page's theorem).
-- statement:
--   **Main theorem (conditional refinement of Page's theorem).**  Suppose the
--   repulsion principle holds with constant `C`, and the constants satisfy the arithmetic
--   compatibility `C > 2 · Q₀^{-ε} · log M`.  Then any two `ε`-exceptional characters with
--   conductors in the window `[Q₀, M]` coincide: there is at most one exceptional character
--   in the window.
--
--   ```lean
--   theorem PageSiegelRepulsion.at_most_one_exceptional    {ε C : ℝ} {Q₀ M : ℕ}
--       (hε : 0 < ε) (hQ₀ : 2 ≤ Q₀) (hM : Q₀ ≤ M)
--       (hthr : 2 * (Q₀ : ℝ) ^ (-ε) * Real.log M < C)
--       {χ₁ χ₂ : QuadraticCharacter}
--       (h₁ : Valid ε Q₀ M χ₁) (h₂ : Valid ε Q₀ M χ₂)
--       (hrep : Repulsion C χ₁ χ₂) :
--       χ₁ = χ₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PageSiegelRepulsion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PageSiegelRepulsion.lean#L122

-- Thm stub generated from Novelty/PageSiegelRepulsion.lean
import Mathlib
import Definitions.Def_Novelty_PageSiegelRepulsion

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

open PageSiegelRepulsion

theorem PageSiegelRepulsion.at_most_one_exceptional    {ε C : ℝ} {Q₀ M : ℕ}
    (hε : 0 < ε) (hQ₀ : 2 ≤ Q₀) (hM : Q₀ ≤ M)
    (hthr : 2 * (Q₀ : ℝ) ^ (-ε) * Real.log M < C)
    {χ₁ χ₂ : QuadraticCharacter}
    (h₁ : Valid ε Q₀ M χ₁) (h₂ : Valid ε Q₀ M χ₂)
    (hrep : Repulsion C χ₁ χ₂) :
    χ₁ = χ₂ := by sorry
