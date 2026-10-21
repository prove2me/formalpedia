-- Prove2me | Theorems.Thm_WolfPack_FlowEngage_proposition_7
-- name    : WolfPack.FlowEngage.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:05.409389+00:00
-- url     : https://prove2.me/theorems/5fecddeb-e57b-45ed-bc80-0c8871645bc2
-- title:
--   Proposition 7, pp. 23–24 (M ≥ 1, N ≥ 2 added) — competition for flow makes engagement succeed where it cannot without flow or with proprietary blocks
-- statement:
--   Work under the standing assumptions of the model (in particular there is at least one unskilled fund, $M \ge 1$) and assume there are at least two skilled funds, $N \ge 2$. Let $\alpha = Nb$, let $K_\eta$ be the smallest number of blocks whose total size reaches $\eta$, let $\hat c$ be the flow-fee function of Definition 5, and write
--   $$\bar c(\eta) = \phi bP_h + \hat c(K_\eta).$$
--   Then:
--
--   1. The delegated game with competition for flow has a maximal success equilibrium.
--   2. For every $\eta \in (b,\alpha]$ and every cost
--   $$c \in \big(\phi bP_h + w(1-\phi)bP_h,\ \bar c(\eta)\big],$$
--   every maximal success equilibrium of the game with competition for flow succeeds at $\eta$ with probability one, while every Nash equilibrium (pure or mixed) of the $\eta$-subgame of the delegated game without competition for flow succeeds with probability zero.
--   3. For every $\eta \in (b,\alpha]$ this cost range is non-empty: $\phi bP_h + w(1-\phi)bP_h < \bar c(\eta)$.
--   4. For every $\eta \in (b,\alpha]$ and every cost $c \in \big(bP_h,\ \bar c(\eta)\big]$, every maximal success equilibrium of the game with competition for flow succeeds at $\eta$ with probability one, while every Nash equilibrium of the $\eta$-subgame of the proprietary blocks game succeeds with probability zero.
--   5. If $M + N > 2/w$, then $bP_h < \bar c(\eta)$ for some $\eta \in (b,\alpha]$.
--
--   This is the paper's headline result: the prospect of attracting the delegated capital of non-engaging funds makes collective engagement succeed over cost ranges where it is impossible when funds are evaluated without flows, and, when there are enough funds, even where it is impossible for funds investing only their own money.
--
--   **Formalization Note.** Two hypotheses are added to the printed statement and disclosed. $M \ge 1$ (a standing assumption of the model file): with $M = 0$ and $K_\eta = N$ one has $\hat c(N) = w(1-\phi)bP_h$ and the range of part 3 is empty. $N \ge 2$: with $N = 1$ there is no $\eta \in (b, \alpha]$ and part 5 fails. "$\eta \le \alpha$" is read on the support $(b, U]$ of $\eta$. "Success is impossible" in a comparison game means that every Nash equilibrium of its $\eta$-subgame has success probability zero; "engagement succeeds" refers to every maximal success equilibrium of the flow game, whose existence is part 1. Actions are `Bool` with `true` = engage.
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), pp. 23–24 (PDF 24–25), Proposition 7; proof pp. A10–A11 (PDF 45–46)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WolfPack.FlowEngage

/-- **Proposition 7** (pp. 23–24), competition for flow ameliorates underengagement.
Actions are `Bool`, `true` = engage; `thr η = φ b Ph + ĉ(Kη)`. Assumes the standing
assumptions (including the disclosed `M ≥ 1`) and the added `N ≥ 2` (with `N = 1` the
range `η ∈ (b, α]` is empty and the "for some η" clause fails).
1. A maximal success equilibrium of the game with competition for flow exists.
2. For each `η ∈ (b, α]`, if `c ∈ (φ b Ph + w (1 − φ) b Ph, thr η]`, every maximal success
   equilibrium of the flow game succeeds with probability one at `η`, while every Nash
   equilibrium of the `η`-subgame of the delegated game without competition for flow
   has success probability zero.
3. For each `η ∈ (b, α]` this cost range is non-empty.
4. For each `η ∈ (b, α]`, if `c ∈ (b Ph, thr η]`, every maximal success equilibrium of the
   flow game succeeds with probability one at `η`, while every Nash equilibrium of the
   `η`-subgame of the proprietary blocks game has success probability zero.
5. If `M + N > 2 / w`, the range `(b Ph, thr η]` is non-empty for some `η ∈ (b, α]`. -/
theorem proposition_7 (p : Params) (hp : p.Standing) (hN : 2 ≤ p.N) : (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ) ∧ (∀ eta ∈ Set.Ioc p.b (alpha p), p.c ∈ Set.Ioc (p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph) (p.phi * p.b * p.Ph + chat p (Keta p eta)) → (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ → successProb p eta (σ eta) = 1) ∧ (∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .noFlow) τ → successProb p eta τ = 0)) ∧ (∀ eta ∈ Set.Ioc p.b (alpha p), p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph < p.phi * p.b * p.Ph + chat p (Keta p eta)) ∧ (∀ eta ∈ Set.Ioc p.b (alpha p), p.c ∈ Set.Ioc (p.b * p.Ph) (p.phi * p.b * p.Ph + chat p (Keta p eta)) → (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ → successProb p eta (σ eta) = 1) ∧ (∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .proprietary) τ → successProb p eta τ = 0)) ∧ (2 / p.w < (p.M : ℝ) + p.N → ∃ eta ∈ Set.Ioc p.b (alpha p), p.b * p.Ph < p.phi * p.b * p.Ph + chat p (Keta p eta)) := by sorry

end WolfPack.FlowEngage
