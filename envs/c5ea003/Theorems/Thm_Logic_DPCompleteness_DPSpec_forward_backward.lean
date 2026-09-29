-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_forward_backward
-- name    : Logic.DPCompleteness.DPSpec.forward_backward
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:26:09.413296+00:00
-- url     : https://prove2.me/theorems/e1fa8cac-837c-428c-a19e-7da39aa2a603
-- title:
--   Forward–backward decomposition.
-- statement:
--   **Forward–backward decomposition.** Splitting an optimal run at any intermediate stage `k`
--   gives the optimum of forward value plus backward value.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.forward_backward(D : DPSpec S W) :
--       ∀ (m k : ℕ),
--         (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => D.val (k + m) s) =
--           (Finset.univ : Finset S).sup' Finset.univ_nonempty
--             (fun s => D.val k s + D.bval k m s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompleteness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompleteness.lean#L289

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



/-! ## DP runs -/






variable [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]



/-! ## Existence of DP runs -/


variable [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]








/-! ## Backward values and the forward–backward decomposition -/


variable [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

theorem Logic.DPCompleteness.DPSpec.forward_backward(D : DPSpec S W) :
    ∀ (m k : ℕ),
      (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => D.val (k + m) s) =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun s => D.val k s + D.bval k m s) := by sorry
