-- Prove2me | Theorems.Thm_SpernerNash_regretA_le_of_support
-- name    : SpernerNash.regretA_le_of_support
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:51:10.646523+00:00
-- url     : https://prove2.me/theorems/ce157254-e682-4bcb-907b-20edacaa765a
-- title:
--   RegretA le of support
-- statement:
--   Formal statement of `SpernerNash.regretA_le_of_support` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SpernerNash.regretA_le_of_support[Fintype A] [Fintype B] [Nonempty A]
--       (pA : A → B → ℝ) (σ₁ : A → ℝ) (σ₂ : B → ℝ) (ε : ℝ)
--       (hσ : σ₁ ∈ stdSimplex ℝ A)
--       (h : ∀ a, 0 < σ₁ a → brValA pA σ₂ - purePayA pA a σ₂ ≤ ε) :
--       regretA pA σ₁ σ₂ ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/GameTheory/SpernerNash.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/GameTheory/SpernerNash.lean#L156

-- Thm stub generated from Geometry/GameTheory/SpernerNash.lean
import Mathlib
import Definitions.Def_Geometry_GameTheory_SpernerNash
/-
# Sperner's Lemma Directly Yields Approximate Nash Equilibria

This module proves that **Sperner's lemma** directly yields approximate Nash
equilibria for finite two-player games, *without* invoking any topological
fixed-point theorem (Brouwer / Kakutani) and without invoking Nash's existence
theorem.

The development is organized as:

* Mixed strategies as the standard simplex `stdSimplex ℝ A`.
* Expected payoffs `payA`, `payB`, pure-strategy payoffs, best-response value
  and regret.
* Elementary analytic facts: bilinearity / Lipschitz bounds for the expected
  payoff (with explicit constants in terms of the payoff bound `L`), and the
  key *regret-from-support* lemma.
* The best-response Sperner labeling and the proof that the labeled pure
  strategy is genuinely a best response (properness of the labeling).
* The combinatorial core (`spernerCore`): a fully-labeled cell of a fine
  triangulation produces a profile with approximate complementary slackness.
  This is exactly the place where Sperner's lemma is applied; it is the only
  classical combinatorial input and uses *no* fixed-point theorem.
* The main theorem `sperner_yields_approx_nash`, deduced analytically from
  `spernerCore` and the regret-from-support lemma.

## Main result

`sperner_yields_approx_nash`: for payoffs bounded by `L`, and every `δ > 0`,
there is a mixed-strategy profile whose regret for both players is at most
`C * L * δ`, where `C` depends only on `|A|` and `|B|`.
-/


open scoped BigOperators
open Finset

open SpernerNash

variable {A B : Type*}

/-! ## Expected payoffs, best response and regret -/









/-! ## Elementary identities -/



/-! ## Best-response value: basic facts -/





/-! ## Lipschitz bounds for the expected payoff

These are the elementary real-analysis facts replacing any appeal to continuity
machinery: the pure-strategy payoff is `L`-Lipschitz in the opponent's mixed
strategy with respect to the `ℓ¹` distance. -/



/-! ## The regret-from-support lemma

This is the analytic heart of the extraction step.  If a mixed strategy `σ₁`
only places weight on pure strategies whose payoff against `σ₂` is within `ε` of
the best response value, then the regret of `σ₁` against `σ₂` is at most `ε`.
This is exactly the *approximate complementary slackness* condition, and is what
a fully-labeled Sperner cell provides geometrically. -/

theorem SpernerNash.regretA_le_of_support[Fintype A] [Fintype B] [Nonempty A]
    (pA : A → B → ℝ) (σ₁ : A → ℝ) (σ₂ : B → ℝ) (ε : ℝ)
    (hσ : σ₁ ∈ stdSimplex ℝ A)
    (h : ∀ a, 0 < σ₁ a → brValA pA σ₂ - purePayA pA a σ₂ ≤ ε) :
    regretA pA σ₁ σ₂ ≤ ε := by sorry
