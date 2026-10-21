-- Prove2me | Theorems.Thm_WolfPack_FlowEngage_proposition_4
-- name    : WolfPack.FlowEngage.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:50.99598+00:00
-- url     : https://prove2.me/theorems/3ab09ea1-b5eb-4f4f-95f8-2f2fdd138e2f
-- title:
--   Proposition 4, p. 20 — maximal success equilibrium with competition for flow: success iff η ≤ α and c ≤ φbPh + ĉ(Kη)
-- statement:
--   Consider the delegated game with competition for flow under the standing assumptions, with $\alpha = Nb$, $K_\eta$ the smallest number of blocks reaching $\eta$, and $\hat c$ the flow-fee function of Definition 5. Then:
--
--   1. There is a maximal success equilibrium $\sigma$ such that for every $\eta \in (b,\alpha]$ with
--   $$c \le \phi bP_h + \hat c(K_\eta),$$
--   $\sigma(\eta)$ is a pure profile in which at least $K_\eta$ funds engage (a $K_\eta$, $L_\eta$ or $N$ profile), and engagement succeeds with probability one.
--   2. Every maximal success equilibrium succeeds with probability one at each such $\eta$.
--   3. For every $\eta \in (b, U]$ with $\eta > \alpha$, or with $c > \phi bP_h + \hat c(K_\eta)$, no fund engages with positive probability in any Nash equilibrium (pure or mixed) of the $\eta$-subgame.
--
--   Unlike the benchmark games, the cost threshold depends on $\eta$ through $K_\eta$: at a given cost, engagement can succeed at some difficulties and not at others.
--
--   **Formalization Note.** The paper's sentence "a maximal success equilibrium is characterized as follows" is rendered as the existence of one with the stated pure profiles, plus two claims about all equilibria: every maximal success equilibrium succeeds where success is possible, and no equilibrium involves engagement elsewhere (the paper notes on p. 20 that mixed equilibria are covered). Actions are `Bool` with `true` = engage.
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), p. 20 (PDF 21), Proposition 4; proof pp. A6–A9 (PDF 41–44)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WolfPack.FlowEngage

/-- **Proposition 4** (p. 20), maximal success equilibrium of the delegated game
with competition for flow (actions `Bool`, `true` = engage).
1. There is a maximal success equilibrium `σ` such that, for every `η ∈ (b, α]` with
   `c ≤ φ b Ph + ĉ(Kη)`, the profile `σ η` is a pure profile in which at least `Kη`
   funds engage (a `Kη`, `Lη` or `N` profile) and engagement succeeds with
   probability one; moreover every maximal success equilibrium succeeds with
   probability one at such `η`.
2. For every `η ∈ (b, U]` with `η > α`, or with `c > φ b Ph + ĉ(Kη)`, in every
   (mixed) Nash equilibrium of the `η`-subgame no fund engages. -/
theorem proposition_4 (p : Params) (hp : p.Standing) : (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ ∧ ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta) → ∃ s : Fin p.N → Bool, Keta p eta ≤ numEngaged s ∧ σ eta = pureLottery s ∧ successProb p eta (σ eta) = 1) ∧ (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ → ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta) → successProb p eta (σ eta) = 1) ∧ (∀ eta ∈ Set.Ioc p.b p.U, (alpha p < eta ∨ p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c) → ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .flow) τ → ∀ i, τ i true = 0) := by sorry

end WolfPack.FlowEngage
