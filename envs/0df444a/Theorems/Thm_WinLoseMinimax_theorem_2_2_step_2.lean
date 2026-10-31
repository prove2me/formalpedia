-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_2_2_step_2
-- name    : WinLoseMinimax.theorem_2_2_step_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:45.953449+00:00
-- url     : https://prove2.me/theorems/f5e33a26-7bd3-48bf-a3ca-c1f7e4d7c553
-- title:
--   Proof of Theorem 2.2, Step 2, p.6 (= Theorem 3.1, Step 2, p.12) — truncated values $v_n$ decrease to $v\in[0,1]$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game and identify $T$ with the positive integers. For $n\ge1$ let $G_n=(S,T_n,\pi_n)$ be the subgame in which player 2 is restricted to the first $n$ pure strategies. Then:
--
--   1. for every $n$, the game $G_n$ has a value $v_n$ (both players have optimal mixed strategies guaranteeing $v_n$);
--   2. the sequence $(v_n)_{n\ge1}$ is non-increasing and converges to some $v\in[0,1]$.
--
--   The same step appears verbatim in the proofs of Theorem 2.2 (p.6) and Theorem 3.1 (p.12); its limit $v$ is the common value that Steps 3 and 4 identify with both sides of the minimax equation.
--
--   **Formalization Note** The identification is an arbitrary enumeration $e:\mathbb N\simeq T$ and $T_n=\{e(0),\dots,e(n-1)\}$. Since the value of a game is unique, part 2 is stated for every sequence $(v_n)$ of values.
--
--   Differences from the source:
--   - encoding: T identified with the positive integers; Tₙ = the first n pure strategies, n = 1, 2, … → an arbitrary enumeration `e : ℕ ≃ T` (implies T countably infinite); Tₙ = `e '' Set.Iio n` = {e 0, …, e (n−1)}, n ≥ 1; reason: the paper's identification is arbitrary; the statement holds for every one
--   - reading: Gₙ "has a value vₙ" → `HasValue (trunc π e n) (v n)`: some p guarantees ≥ vₙ against every q and some q holds player 1 to ≤ vₙ against every p; reason: the proof uses optimal strategies qₙ and pₙ (Steps 3, 4); this is the finite-game value of §1, the stronger reading
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - generalization: Step 2 inside the proof of Theorem 2.2 (B¹_down(G) ascending-union closed) and of Theorem 3.1 (G LNG-free); T countably infinite → no ascending-union or LNG-freeness hypothesis; S countably infinite, T enumerated by e; reason: the step's proof uses neither hypothesis; adding either back gives the paper's two instances
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 2.2, Step 2, p.6; proof of Theorem 3.1, Step 2, p.12

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal
open Filter
open scoped Topology

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 2.2, Step 2: the truncated games have values decreasing to a limit.**
Holzman, arXiv:2310.19314v1, proof of Theorem 2.2, Step 2, p.6 (repeated verbatim as Step 2 of the
proof of Theorem 3.1, p.12): let `G = (S, T, π)` be a countable game, with `T` identified with the
positive integers, and let `Gₙ = (S, Tₙ, πₙ)` be the subgame obtained by restricting player 2 to
the first `n` pure strategies. Then for every `n` the game `Gₙ` has a value `vₙ`, and the
sequence `(vₙ)` is non-increasing and converges to some `v ∈ [0, 1]`.

**Formalization Note.** The identification of `T` with the positive integers is an arbitrary
enumeration `e : ℕ ≃ T` (the statement holds for every one); `Gₙ` is `trunc π e n` for `n ≥ 1`
(player 2 restricted to `e 0, …, e (n-1)`). "Has a value" is `HasValue` (value with optimal
strategies on both sides). The value of a game is unique, so the second clause is stated for every
sequence of values. Values live in `ℝ≥0∞`. The step is stated without the ascending-union
hypothesis of Theorem 2.2 (and without the LNG-freeness standing in the proof of Theorem 3.1),
which its proof does not use. -/
theorem theorem_2_2_step_2 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    (π : S → T → Bool) (e : ℕ ≃ T) :
    (∀ n : ℕ, 1 ≤ n → ∃ v : ℝ≥0∞, HasValue (trunc π e n) v) ∧
      ∀ v : ℕ → ℝ≥0∞, (∀ n : ℕ, 1 ≤ n → HasValue (trunc π e n) (v n)) →
        AntitoneOn v (Set.Ici 1) ∧ ∃ w : ℝ≥0∞, w ≤ 1 ∧ Tendsto v atTop (𝓝 w) := by sorry

end WinLoseMinimax
