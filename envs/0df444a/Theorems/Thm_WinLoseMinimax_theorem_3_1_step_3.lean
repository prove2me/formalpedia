-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_3_1_step_3
-- name    : WinLoseMinimax.theorem_3_1_step_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:52.390833+00:00
-- url     : https://prove2.me/theorems/b55236a6-8dd3-49e0-9309-79b6d5843ad0
-- title:
--   Proof of Theorem 3.1, Step 3, p.12 — $\inf_q\sup_p\pi_{\mathrm{mix}}(p,q)\le v$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$, $T$ countably infinite), let $t_1,t_2,\dots$ enumerate $T$, let $v_n$ be the value of the truncated game $G_n$ in which player 2 is restricted to $t_1,\dots,t_n$, and let $v=\lim_n v_n$ (Step 2). Then
--
--   $$\inf_{q\in\Delta(T)}\sup_{p\in\Delta(S)}\pi_{\mathrm{mix}}(p,q)\le v .$$
--
--   Together with Step 4 this shows that $v$ is the $\varepsilon$-value of $G$.
--
--   **Formalization Note** The data of Step 2 are hypotheses: the enumeration $e:\mathbb N\simeq T$, values $v_n$ (with optimal strategies) of the truncations for $n\ge1$, and their limit.
--
--   Differences from the source:
--   - encoding: T identified with the positive integers; Tₙ = the first n pure strategies, n = 1, 2, … → an arbitrary enumeration `e : ℕ ≃ T` (implies T countably infinite); Tₙ = `e '' Set.Iio n` = {e 0, …, e (n−1)}, n ≥ 1; reason: the paper's identification is arbitrary; the statement holds for every one
--   - reading: Gₙ "has a value vₙ" → `HasValue (trunc π e n) (v n)`: some p guarantees ≥ vₙ against every q and some q holds player 1 to ≤ vₙ against every p; reason: the proof uses optimal strategies qₙ and pₙ (Steps 3, 4); this is the finite-game value of §1, the stronger reading
--   - encoding: "the v of Step 2" → hypotheses: enumeration `e`, values `v n` of `trunc π e n` for n ≥ 1, limit `w` with `Tendsto v atTop (𝓝 w)`; reason: the value of a game is unique, so these hypotheses pin down exactly the paper's vₙ and v
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - generalization: standing assumption of the proof of Theorem 3.1: G LNG-free → no LNG-freeness hypothesis; reason: the step's proof (p.7 second part of Step 3 of Theorem 2.2) does not use it; adding it back gives the paper's statement
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S]`, and T through `e : ℕ ≃ T`; reason: exactly countably infinite S and T
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 3.1, Step 3, p.12

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal
open Filter
open scoped Topology

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 3.1, Step 3: `inf sup ≤ v`.** Holzman, arXiv:2310.19314v1, proof of
Theorem 3.1, Step 3, p.12: `inf_{q ∈ ∆(T)} sup_{p ∈ ∆(S)} π_mix(p, q) ≤ v`, where `v` is the limit
of the values `vₙ` of the truncated games `Gₙ` from Step 2.

**Formalization Note.** The data of Step 2 are hypotheses: an enumeration `e : ℕ ≃ T`, values
`v n` of the truncated games `trunc π e n` for `n ≥ 1` (with optimal strategies, `HasValue`), and
their limit `w`. "Countable game" means countably infinite `S` and `T`. The LNG-freeness standing
in the proof of Theorem 3.1 is not assumed: this step does not use it (it is also the second part
of Step 3 of the proof of Theorem 2.2, p.7). -/
theorem theorem_3_1_step_3 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    (π : S → T → Bool) (e : ℕ ≃ T) (v : ℕ → ℝ≥0∞)
    (hv : ∀ n : ℕ, 1 ≤ n → HasValue (trunc π e n) (v n))
    (w : ℝ≥0∞) (hlim : Tendsto v atTop (𝓝 w)) :
    (⨅ q : PMF T, ⨆ p : PMF S, payoff π p q) ≤ w := by sorry

end WinLoseMinimax
