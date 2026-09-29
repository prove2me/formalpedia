-- Prove2me | Theorems.Thm_HoggattHierarchy_inv_factorial_strictLogConcave
-- name    : HoggattHierarchy.inv_factorial_strictLogConcave
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:46.902105+00:00
-- url     : https://prove2.me/theorems/e091c0ce-dd14-4595-8cf9-b612d271b8f6
-- title:
--   Inv factorial strictLogConcave
-- statement:
--   Formal statement of `HoggattHierarchy.inv_factorial_strictLogConcave` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HoggattHierarchy.inv_factorial_strictLogConcave:
--       StrictLogConcave (fun n => 1 / (n.factorial : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/HoggattTrichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/HoggattTrichotomy.lean#L234

-- Thm stub generated from Novelty/HoggattTrichotomy.lean
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

theorem HoggattHierarchy.inv_factorial_strictLogConcave:
    StrictLogConcave (fun n => 1 / (n.factorial : ℝ)) := by sorry
