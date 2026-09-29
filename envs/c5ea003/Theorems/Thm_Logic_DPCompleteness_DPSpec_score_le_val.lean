-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_score_le_val
-- name    : Logic.DPCompleteness.DPSpec.score_le_val
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:47.301565+00:00
-- url     : https://prove2.me/theorems/20749734-8499-4245-904e-a4ace84d8ef5
-- title:
--   Domination.
-- statement:
--   **Domination.** Every labelling scores at most the DP value at its endpoint.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.score_le_val(D : DPSpec S W) (f : ℕ → S) : ∀ n : ℕ, D.score f n ≤ D.val n (f n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompleteness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompleteness.lean#L118

-- Thm stub generated from Logic/DPCompleteness.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
/-
# Completeness of Dynamic Programming: every labelling is dominated by some DP run

This file develops, from scratch, a general theory of *layered dynamic programming*
(the Viterbi / Bellman shortest-path schema) over an arbitrary finite state space `S`
and an arbitrary linearly ordered cancellative additive monoid `W` of weights, and
proves the **completeness theorem**:

> every labelling `f : ℕ → S` is dominated by some DP run `g`, i.e. there is a `g`
> all of whose prefixes are DP-optimal and whose total score is at least that of `f`.

Together with the dual **soundness** statement (every DP run is an honest labelling whose
score is exactly the DP value) this gives an exactness theorem: the DP value function is
the greatest element of the set of achievable labelling scores.

We additionally prove
* the **Bellman optimality principle** (`IsDPRun` is inherited by every prefix of an
  end-optimal labelling),
* the **forward-backward decomposition** relating the forward value function to a
  backward value function at any intermediate stage,
* **monotonicity** of the value function in the specification.

Everything is stated for a general weight monoid, so it specialises simultaneously to
max-plus (longest path), min-plus (shortest path, by using the order dual), and
Viterbi-style probabilistic decoding.
-/


open Logic.DPCompleteness

/-! ## Generic `sup'` lemmas -/


variable {ι W : Type*} [LinearOrder W] [AddCommMonoid W] [AddLeftMono W]




/-! ## The DP specification -/


open DPSpec

variable {S W : Type*} [AddCommMonoid W]






variable [Fintype S] [Nonempty S] [LinearOrder W]




variable [AddLeftMono W]

theorem Logic.DPCompleteness.DPSpec.score_le_val(D : DPSpec S W) (f : ℕ → S) : ∀ n : ℕ, D.score f n ≤ D.val n (f n) := by sorry
