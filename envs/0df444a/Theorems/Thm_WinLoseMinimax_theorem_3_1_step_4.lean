-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_3_1_step_4
-- name    : WinLoseMinimax.theorem_3_1_step_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:46.065301+00:00
-- url     : https://prove2.me/theorems/67d86892-5fee-4cfe-ae2c-9d72230854b1
-- title:
--   Proof of Theorem 3.1, Step 4, pp.12–13 — $\sup_p\inf_q\pi_{\mathrm{mix}}(p,q)\ge v$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable ($S$, $T$ countably infinite) LNG-free game, let $t_1,t_2,\dots$ enumerate $T$, let $v_n$ be the value of the truncated game $G_n$ in which player 2 is restricted to $t_1,\dots,t_n$, and let $v=\lim_n v_n$ (Step 2). Then
--
--   $$\sup_{p\in\Delta(S)}\inf_{q\in\Delta(T)}\pi_{\mathrm{mix}}(p,q)\ge v .$$
--
--   With Step 3 this proves Theorem 3.1 for countable games: both sides of the minimax equation equal $v$.
--
--   **Formalization Note** The data of Step 2 are hypotheses, as in Step 3. LNG-freeness and countability are the standing assumptions of the proof (p.11).
--
--   Differences from the source:
--   - encoding: T identified with the positive integers; Tₙ = the first n pure strategies, n = 1, 2, … → an arbitrary enumeration `e : ℕ ≃ T` (implies T countably infinite); Tₙ = `e '' Set.Iio n` = {e 0, …, e (n−1)}, n ≥ 1; reason: the paper's identification is arbitrary; the statement holds for every one
--   - reading: Gₙ "has a value vₙ" → `HasValue (trunc π e n) (v n)`: some p guarantees ≥ vₙ against every q and some q holds player 1 to ≤ vₙ against every p; reason: the proof uses optimal strategies qₙ and pₙ (Steps 3, 4); this is the finite-game value of §1, the stronger reading
--   - encoding: "the v of Step 2" → hypotheses: enumeration `e`, values `v n` of `trunc π e n` for n ≥ 1, limit `w` with `Tendsto v atTop (𝓝 w)`; reason: the value of a game is unique, so these hypotheses pin down exactly the paper's vₙ and v
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S]`, and T through `e : ℕ ≃ T`; reason: exactly countably infinite S and T
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 3.1, Step 4, pp.12–13; standing assumptions p.11

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal
open Filter
open scoped Topology

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 3.1, Step 4: `sup inf ≥ v`.** Holzman, arXiv:2310.19314v1, proof of
Theorem 3.1, Step 4, pp.12–13: for a countable LNG-free game,
`sup_{p ∈ ∆(S)} inf_{q ∈ ∆(T)} π_mix(p, q) ≥ v`, where `v` is the limit of the values `vₙ` of the
truncated games `Gₙ` from Step 2.

**Formalization Note.** The data of Step 2 are hypotheses: an enumeration `e : ℕ ≃ T`, values
`v n` of `trunc π e n` for `n ≥ 1` (`HasValue`), and their limit `w`. The standing assumptions of
the proof (LNG-free, countable = countably infinite `S` and `T`, p.11) are hypotheses. -/
theorem theorem_3_1_step_4 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    (π : S → T → Bool) (hfree : LNGFree π) (e : ℕ ≃ T) (v : ℕ → ℝ≥0∞)
    (hv : ∀ n : ℕ, 1 ≤ n → HasValue (trunc π e n) (v n))
    (w : ℝ≥0∞) (hlim : Tendsto v atTop (𝓝 w)) :
    w ≤ ⨆ p : PMF S, ⨅ q : PMF T, payoff π p q := by sorry

end WinLoseMinimax
