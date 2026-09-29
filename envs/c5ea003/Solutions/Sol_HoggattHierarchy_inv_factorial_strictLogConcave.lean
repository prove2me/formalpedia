-- Prove2me | solution 1 for HoggattHierarchy.inv_factorial_strictLogConcave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:02:13.165388+00:00
-- url     : https://prove2.me/submissions/a025b7df-2df2-4672-a520-2183c5f96e32

-- Sol generated from Novelty/HoggattTrichotomy.lean
import Mathlib
import Definitions.Def_Novelty_HoggattTrichotomy

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

open HoggattHierarchy

/-! ## Log-behaviour predicates over `ℝ` -/






/-! ## The ratio criterion

A positive real sequence with strictly increasing consecutive ratios is
strictly log-convex.  This isolates the "ratio amplification" mechanism. -/


/-! ## The Möbius trichotomy engine

Everything below flows from a single observation: under the recurrence, the
consecutive ratio is the Möbius function `(γ n + δ)/(α n + β)`. -/

/-- Under the multiplicative recurrence, the consecutive ratio equals the
Möbius function `(γ n + δ)/(α n + β)`. -/
theorem ratio_eq_mobius {a : ℕ → ℝ} {α β γ δ : ℝ}
    (hpos : ∀ n, 0 < a n)
    (hden : ∀ n : ℕ, 0 < α * n + β)
    (hrec : ∀ n : ℕ, (α * n + β) * a (n + 1) = (γ * n + δ) * a n) :
    ∀ m : ℕ, a (m + 1) / a m = (γ * m + δ) / (α * m + β) := by
  intro m
  rw [div_eq_div_iff (hpos m).ne' (hden m).ne']
  linear_combination hrec m



/-- **Strictly log-concave regime** (`Δ = γβ − αδ < 0`). -/
theorem strictLogConcave_of_recurrence {a : ℕ → ℝ} {α β γ δ : ℝ}
    (hpos : ∀ n, 0 < a n)
    (hden : ∀ n : ℕ, 0 < α * n + β)
    (hrec : ∀ n : ℕ, (α * n + β) * a (n + 1) = (γ * n + δ) * a n)
    (hdisc : γ * β < α * δ) :
    StrictLogConcave a := by
  have hratio := ratio_eq_mobius hpos hden hrec
  intro n
  have key : a (n + 2) / a (n + 1) < a (n + 1) / a n := by
    rw [hratio n, hratio (n + 1), div_lt_div_iff₀ (hden (n + 1)) (hden n)]
    push_cast; nlinarith [hdisc]
  rw [div_lt_div_iff₀ (hpos (n + 1)) (hpos n)] at key
  nlinarith [key]


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


open HoggattHierarchy in
theorem solution:
    StrictLogConcave (fun n => 1 / (n.factorial : ℝ)) := by
  apply strictLogConcave_of_recurrence
      (α := 1) (β := 1) (γ := 0) (δ := 1)
  · intro n
    have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    positivity
  · intro n; positivity
  · intro n
    have h : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      have := Nat.factorial_succ n; push_cast [this]; ring
    have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [h]; field_simp; ring
  · norm_num
