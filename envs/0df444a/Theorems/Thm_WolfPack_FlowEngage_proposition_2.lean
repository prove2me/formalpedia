-- Prove2me | Theorems.Thm_WolfPack_FlowEngage_proposition_2
-- name    : WolfPack.FlowEngage.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:54.198773+00:00
-- url     : https://prove2.me/theorems/05df982b-aade-40a5-a959-09590a384b3f
-- title:
--   Proposition 2, p. 15 — proprietary blocks game: a Kη profile succeeds iff η ≤ α and c ≤ bPh
-- statement:
--   Consider the proprietary blocks game under the standing assumptions: the same funds, blocks and costs, but $\phi = 1$, so funds manage only their own money and fees and flows play no role. Let $\alpha = Nb$ and $K_\eta$ be the smallest number of blocks reaching $\eta$. Then:
--
--   1. There is a maximal success equilibrium $\sigma$ such that for every $\eta \in (b,\alpha]$ with
--   $$c \le bP_h,$$
--   $\sigma(\eta)$ is a pure profile in which exactly $K_\eta$ funds engage, and engagement succeeds with probability one.
--   2. Every maximal success equilibrium succeeds with probability one at each such $\eta$.
--   3. For every $\eta \in (b,U]$ with $\eta > \alpha$, or with $c > bP_h$, no fund engages with positive probability in any Nash equilibrium of the $\eta$-subgame.
--
--   A fund engages only when it is pivotal, and then only if its share of the value created, $bP_h$, covers its cost. This is the second benchmark of Proposition 7.
--
--   **Formalization Note.** Actions are `Bool` with `true` = engage. The proprietary game is the model with the proprietary fraction set to $1$ and all other parameters unchanged (p. 15, footnote 14). The "no engagement" half is stated for every mixed Nash equilibrium.
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), p. 15 (PDF 16), Proposition 2; proof pp. A1–A2 (PDF 36–37)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WolfPack.FlowEngage

/-- **Proposition 2** (p. 15), maximal success equilibrium of the proprietary blocks game (φ = 1)
(actions `Bool`, `true` = engage).
1. There is a maximal success equilibrium `σ` such that, for every `η ∈ (b, α]` with
   `c ≤ b Ph`, the profile `σ η` is a pure `Kη` profile (exactly `Kη` funds
   engage) and engagement succeeds with probability one; moreover every maximal
   success equilibrium succeeds with probability one at such `η`.
2. For every `η ∈ (b, U]` with `η > α`, or with `c > b Ph`, in every (mixed)
   Nash equilibrium of the `η`-subgame no fund engages. -/
theorem proposition_2 (p : Params) (hp : p.Standing) : (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .proprietary σ ∧ ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.b * p.Ph → ∃ s : Fin p.N → Bool, numEngaged s = Keta p eta ∧ σ eta = pureLottery s ∧ successProb p eta (σ eta) = 1) ∧ (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .proprietary σ → ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.b * p.Ph → successProb p eta (σ eta) = 1) ∧ (∀ eta ∈ Set.Ioc p.b p.U, (alpha p < eta ∨ p.b * p.Ph < p.c) → ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .proprietary) τ → ∀ i, τ i true = 0) := by sorry

end WolfPack.FlowEngage
