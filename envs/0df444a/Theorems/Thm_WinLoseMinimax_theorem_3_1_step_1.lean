-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_3_1_step_1
-- name    : WinLoseMinimax.theorem_3_1_step_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:57.626137+00:00
-- url     : https://prove2.me/theorems/83d33630-a4b2-4b5c-bf4b-872fb87e6e19
-- title:
--   Proof of Theorem 3.1, Step 1, p.12 — each $z\in\mathrm{cl}(B^1(G))$ is almost realized by a finitely supported rational mixed strategy
-- statement:
--   Let $G=(S,T,\pi)$ be a countable ($S$, $T$ countably infinite) LNG-free game. View each row $(\pi(s,t))_{t\in T}$ as a point of $\{0,1\}^T$ with the product topology, and let $\mathrm{cl}(\mathcal B^1(G))$ be the closure of the set of rows. Let $\varepsilon>0$ and $z\in\mathrm{cl}(\mathcal B^1(G))$. Then there is $p\in\Delta(S)$ such that for all $t\in T$
--
--   $$z_t=1\ \Longrightarrow\ \pi_{\mathrm{mix}}(p,t)\ge1-\varepsilon.\tag{5}$$
--
--   Moreover, $p$ may be chosen with finite support and with all probabilities $p_s$ rational.
--
--   These are the standing assumptions of the proof of Theorem 3.1 ("we assume that $G$ is LNG-free … we also assume that $G$ is countable", p.11). The step lets limit points of rows be replaced by mixed strategies of the original game in Step 4.
--
--   **Formalization Note** $\varepsilon$ is real and $1-\varepsilon$ enters $[0,\infty]$ through `ENNReal.ofReal`; for $\varepsilon\ge1$ both (5) and its Lean form are trivial. $\pi_{\mathrm{mix}}(p,t)$ is the payoff against the pure strategy $t$. "Rational" means each $p_s$ is the image of a rational number.
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: ∆(X): probability distributions on X with at most countable support (p.3) → `PMF X`; reason: every `PMF` has countable support (`PMF.support_countable`) and every such distribution is a `PMF`; same objects
--   - encoding: real-valued π_mix and real sup/inf → values, `⨆` and `⨅` in `ℝ≥0∞`; reason: all values lie in [0, 1] and the families are non-empty, where the `ℝ≥0∞` sup/inf coincide with the real ones
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: z = (z₁, z₂, …) ∈ cl(B¹(G)) ⊆ {0,1}^ℕ → `z : T → Bool` in `closure (Set.range π)` for the product topology on `T → Bool`; reason: a row B_s is the function π s; identifying T with ℕ is a homeomorphism
--   - encoding: ε > 0 and the bound 1 − ε → real ε > 0, bound `ENNReal.ofReal (1 - ε)`; reason: for ε < 1 this is 1 − ε; for ε ≥ 1 both bounds are vacuous
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 3.1, Step 1, equation (5), p.12; standing assumptions p.11

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 3.1, Step 1: points of `cl(B¹(G))` are almost realized by mixed
strategies.** Holzman, arXiv:2310.19314v1, proof of Theorem 3.1, Step 1, p.12: let `G` be a
countable LNG-free game, let `ε > 0`, and let `z = (z₁, z₂, …) ∈ cl(B¹(G))`. Then there exists
`p ∈ ∆(S)` such that for all `t ∈ T`: `z_t = 1 ⇒ π_mix(p, t) ≥ 1 − ε`  (5). Moreover, `p` may be
chosen so that its support is finite and all probabilities `p_s` are rational.

**Formalization Note.** The standing assumptions of the proof ("we assume that G is LNG-free …
we also assume that G is countable", p.11) are hypotheses; "countable" means countably infinite
`S` and `T`. `cl(B¹(G))` is the closure of the set of rows `{π s : s ∈ S}` in `T → Bool` with the
product topology. `ε` is a real number and `1 − ε` enters `ℝ≥0∞` through `ENNReal.ofReal`
(for `ε ≥ 1` both sides of (5) are trivial, as in the paper). `π_mix(p, t)` is
`payoff π p (PMF.pure t)`. Rational probabilities: each `p s` is the image of a rational number. -/
theorem theorem_3_1_step_1 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool) (hfree : LNGFree π)
    (ε : ℝ) (hε : 0 < ε) (z : T → Bool) (hz : z ∈ closure (Set.range π)) :
    ∃ p : PMF S, p.support.Finite ∧ (∀ s, ∃ r : ℚ, p s = ENNReal.ofReal (r : ℝ)) ∧
      ∀ t : T, z t = true → ENNReal.ofReal (1 - ε) ≤ payoff π p (PMF.pure t) := by sorry

end WinLoseMinimax
