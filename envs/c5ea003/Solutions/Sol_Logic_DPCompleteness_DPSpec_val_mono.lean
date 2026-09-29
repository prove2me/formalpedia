-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.val_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:58:18.880742+00:00
-- url     : https://prove2.me/submissions/5a9cecf1-71ae-41e4-87ca-0c8b9558f8ed

-- Sol generated from Logic/DPCompleteness.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Theorems.Thm_Logic_DPCompleteness_DPSpec_val_succ
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






/-! ## Monotonicity in the specification -/


variable [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]






open Logic.DPCompleteness in
theorem solution{D D' : DPSpec S W} (hinit : ∀ s, D.init s ≤ D'.init s)
    (hstep : ∀ i s t, D.step i s t ≤ D'.step i s t) :
    ∀ (n : ℕ) (s : S), D.val n s ≤ D'.val n s := by
  intro n
  induction n with
  | zero => intro s; simpa using hinit s
  | succ n ih =>
      intro t
      rw [val_succ, val_succ]
      refine Finset.sup'_le _ _ (fun s _ => ?_)
      exact le_trans (add_le_add (ih s) (hstep n s t))
        (Finset.le_sup' (fun s => D'.val n s + D'.step n s t) (Finset.mem_univ s))
