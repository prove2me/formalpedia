-- Prove2me | solution 1 for Logic.DPCompleteness.sup_p_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:57:24.274893+00:00
-- url     : https://prove2.me/submissions/41a0cdc3-bb0d-47c4-84e4-72333306066c

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

theorem solution(s : Finset ι) (h : s.Nonempty) (f : ι → W) (c : W) :
    s.sup' h f + c = s.sup' h (fun i => f i + c) := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ ?_)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' h f
    rw [he]
    exact Finset.le_sup' (fun i => f i + c) hi
  · intro i hi
    exact add_le_add (Finset.le_sup' f hi) le_rfl
