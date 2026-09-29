-- Prove2me | Definitions.Def_Novelty_HoggattTrichotomy
-- name    : Novelty_HoggattTrichotomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:39.919264+00:00
-- url     : https://prove2.me/theorems/7be66d37-1529-4de0-8ae3-c7c06a1243ac
-- title:
--   Aether Catalog definitions — Novelty_HoggattTrichotomy
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HoggattTrichotomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HoggattTrichotomy.lean by skeleton subtraction
import Mathlib

/-!
# A Möbius trichotomy for the total d-Hoggatt numbers

The *total* d-Hoggatt numbers `H_d(n) = ∑_k H_d(n,k)` obey, for the classical
values of `d`, a first-order *multiplicative* recurrence of the shape
`(α n + β)·H(n+1) = (γ n + δ)·H(n)` with rational coefficients:

* `H_1(n) = 2 ^ n`   satisfies `1·H(n+1) = 2·H(n)`             (`α,β,γ,δ = 0,1,0,2`);
* `H_2(n) = Cₙ`      satisfies `(n+2)·H(n+1) = (4n+2)·H(n)`    (`α,β,γ,δ = 1,2,4,2`).

The previous cycle established the *sharp `d = 1` vs `d = 2` dichotomy*
(log-linear vs strictly log-convex).  Here we identify the exact algebraic
mechanism behind that dichotomy and turn it into a **trichotomy governed by a
single Möbius discriminant** `Δ = γβ − αδ`:

> For any positive real sequence obeying `(α n + β)·a(n+1) = (γ n + δ)·a(n)`
> with `α n + β > 0`, the sign of `Δ = γβ − αδ` controls the log-behaviour:
> `Δ > 0` gives **strict log-convexity**, `Δ = 0` gives **log-linearity**, and
> `Δ < 0` gives **strict log-concavity**.

The key structural fact is that the consecutive ratio `a(n+1)/a(n)` equals the
Möbius function `(γ n + δ)/(α n + β)`, whose forward difference has the
*`n`-independent* numerator `Δ`.  This constant is the abstract source of the
"positive coefficient gap" observed concretely in the Catalan discriminant
identity `(2n+1)(n+3)·Cₙ·Cₙ₊₂ = (n+2)(2n+3)·Cₙ₊₁²`.

The framework then explains a whole family of examples at once:

* Catalan numbers `Cₙ`               (`Δ = 6`)  — strictly log-convex;
* central binomial coefficients `C(2n,n)` (`Δ = 2`) — strictly log-convex;
* factorials `n!`                    (`Δ = 1`)  — strictly log-convex;
* powers `2 ^ n`                     (`Δ = 0`)  — log-linear;
* reciprocal factorials `1/n!`       (`Δ = −1`) — strictly log-concave.

In particular all three regimes of the trichotomy are realized, giving a "sharp
trichotomy" refining the earlier dichotomy.
-/

namespace HoggattHierarchy

/-! ## Log-behaviour predicates over `ℝ` -/

/-- A positive real sequence is *strictly log-convex*: `a(n+1)² < a(n)·a(n+2)`. -/
def StrictLogConvex (a : ℕ → ℝ) : Prop := ∀ n, a (n + 1) ^ 2 < a n * a (n + 2)

/-- A real sequence is *log-linear*: `a(n+1)² = a(n)·a(n+2)`. -/
def LogLinear (a : ℕ → ℝ) : Prop := ∀ n, a (n + 1) ^ 2 = a n * a (n + 2)

/-- A real sequence is *strictly log-concave*: `a(n)·a(n+2) < a(n+1)²`. -/
def StrictLogConcave (a : ℕ → ℝ) : Prop := ∀ n, a n * a (n + 2) < a (n + 1) ^ 2



/-! ## The ratio criterion

A positive real sequence with strictly increasing consecutive ratios is
strictly log-convex.  This isolates the "ratio amplification" mechanism. -/


/-! ## The Möbius trichotomy engine

Everything below flows from a single observation: under the recurrence, the
consecutive ratio is the Möbius function `(γ n + δ)/(α n + β)`. -/






/-! ## Concrete instances

We now feed the classical sequences into the engine.  Each application reduces
to (i) positivity, (ii) the multiplicative recurrence recast over `ℝ`, and
(iii) the numeric sign of the discriminant. -/

/-! ### Auxiliary Catalan facts (recast of the thread's engine) -/



/-! ### `d = 2`: the Catalan totals are strictly log-convex (`Δ = 6`) -/


/-! ### Central binomial coefficients are strictly log-convex (`Δ = 2`) -/


/-! ### Factorials are strictly log-convex (`Δ = 1`) -/


/-! ### `d = 1`: the powers `2 ^ n` are log-linear (`Δ = 0`) -/


/-! ### Reciprocal factorials `1/n!` are strictly log-concave (`Δ = −1`) -/


/-! ## The sharp trichotomy

All three regimes are simultaneously realized by classical sequences, refining
the previously established `d = 1` vs `d = 2` dichotomy into a genuine
trichotomy anchored by the sign of the Möbius discriminant. -/



/-!
-- !-- Lab Notes -- !--

**Hypothesis.**  The previous cycle proved a *sharp dichotomy* — `2 ^ n`
log-linear vs Catalan strictly log-convex — driven by an ad-hoc Catalan
discriminant identity whose two coefficients differed by the constant `3`.  We
hypothesized that this constant gap is not special to Catalan but is the shadow
of a single algebraic invariant attached to the underlying first-order
recurrence, and that its sign should govern a full trichotomy.

**Experiment.**  We abstracted the common shape of the classical recurrences to
`(α n + β)·a(n+1) = (γ n + δ)·a(n)`.  Computing the consecutive ratio gives the
Möbius function `(γ n + δ)/(α n + β)`, whose forward difference has numerator
exactly `Δ = γβ − αδ`, independent of `n` (`ratio_eq_mobius` plus the cross
-multiplied inequalities inside `strictLogConvex_of_recurrence` etc.).  Feeding
in Catalan (`Δ = 6`), central binomials (`Δ = 2`), factorials (`Δ = 1`),
`2 ^ n` (`Δ = 0`), and reciprocal factorials (`Δ = −1`) realizes all three
regimes.

**Analysis.**  The mysterious "constant 3" of the Catalan identity is exactly
the discriminant `Δ = 6` divided by the leading normalization; the general
invariant `Δ = γβ − αδ` is what actually controls log-behaviour.  Strict
convexity/concavity is *strict* precisely because `Δ ≠ 0` makes the ratio
strictly monotone; the log-linear boundary is the codimension-one locus
`Δ = 0`, occupied by the geometric sequence `2 ^ n`.

**Critique.**  Each regime theorem is genuinely strict (`<`, not `≤`) and the
exclusivity lemmas (`not_logLinear`, `not_strictLogConcave`) rule out
degeneracy.  The recurrence hypotheses are load-bearing: dropping positivity of
`α n + β` or of `a` breaks the ratio computation.  No result is proved by pure
`decide`/`norm_num`; the engine uses the ratio identity plus cross-multiplied
`nlinarith` steps.

**Synthesis.**  A single scalar `Δ = γβ − αδ` unifies the log-convexity theory
of the classical Hoggatt totals and of the surrounding combinatorial sequences,
upgrading the earlier dichotomy to a sharp, sign-indexed trichotomy.
-/

end HoggattHierarchy


