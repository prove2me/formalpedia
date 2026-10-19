-- Prove2me | Theorems.Thm_WolfPack_FlowEngage_proposition_3
-- name    : WolfPack.FlowEngage.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:52.317979+00:00
-- url     : https://prove2.me/theorems/2e9a0d26-d8a7-45f0-86a4-fb14b6e2094b
-- title:
--   Proposition 3, p. 17 — delegated game without flow: a Kη profile succeeds iff η ≤ α and c ≤ φbPh + w(1 − φ)bPh
-- statement:
--   Consider the delegated game without competition for flow under the standing assumptions: each fund keeps its own delegated capital whatever happens. Let $\alpha = Nb$ and $K_\eta$ be the smallest number of blocks reaching $\eta$. Then:
--
--   1. There is a maximal success equilibrium $\sigma$ such that for every $\eta \in (b,\alpha]$ with
--   $$c \le \phi bP_h + w(1-\phi)bP_h,$$
--   $\sigma(\eta)$ is a pure profile in which exactly $K_\eta$ funds engage, and engagement succeeds with probability one.
--   2. Every maximal success equilibrium succeeds with probability one at each such $\eta$.
--   3. For every $\eta \in (b,U]$ with $\eta > \alpha$, or with $c > \phi bP_h + w(1-\phi)bP_h$, no fund engages with positive probability in any Nash equilibrium of the $\eta$-subgame.
--
--   The threshold is smaller than the proprietary threshold $bP_h$ because $\phi<1$ and $w<1$: delegation without flow reduces engagement incentives. It is one of the two benchmarks of Proposition 7.
--
--   **Formalization Note.** Actions are `Bool` with `true` = engage. The "no engagement" half is stated for every mixed Nash equilibrium.
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), p. 17 (PDF 18), Proposition 3; proof pp. A2–A3 (PDF 37–38)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WolfPack.FlowEngage

/-- **Proposition 3** (p. 17), maximal success equilibrium of the delegated game without competition for flow
(actions `Bool`, `true` = engage).
1. There is a maximal success equilibrium `σ` such that, for every `η ∈ (b, α]` with
   `c ≤ φ b Ph + w (1 − φ) b Ph`, the profile `σ η` is a pure `Kη` profile (exactly `Kη` funds
   engage) and engagement succeeds with probability one; moreover every maximal
   success equilibrium succeeds with probability one at such `η`.
2. For every `η ∈ (b, U]` with `η > α`, or with `c > φ b Ph + w (1 − φ) b Ph`, in every (mixed)
   Nash equilibrium of the `η`-subgame no fund engages. -/
theorem proposition_3 (p : Params) (hp : p.Standing) : (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .noFlow σ ∧ ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph → ∃ s : Fin p.N → Bool, numEngaged s = Keta p eta ∧ σ eta = pureLottery s ∧ successProb p eta (σ eta) = 1) ∧ (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .noFlow σ → ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph → successProb p eta (σ eta) = 1) ∧ (∀ eta ∈ Set.Ioc p.b p.U, (alpha p < eta ∨ p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph < p.c) → ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .noFlow) τ → ∀ i, τ i true = 0) := by sorry

end WolfPack.FlowEngage
