-- Prove2me | Theorems.Thm_WolfPack_FlowEngage_lemma_2
-- name    : WolfPack.FlowEngage.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:47.123397+00:00
-- url     : https://prove2.me/theorems/ec6d3aea-483f-44e5-9ac6-58d5dfb53690
-- title:
--   Lemma 2, p. 19 (1(c) with c ≤ ĉ(N), as its proof shows) — Kη, Lη and N profiles are subgame equilibria of the flow game
-- statement:
--   Consider the delegated game with competition for flow under the standing assumptions, and fix a difficulty $\eta \in (b, \alpha]$, where $\alpha = Nb$. Write $K_\eta$ for the smallest number of blocks whose total size reaches $\eta$, and $\hat c$ for the flow-fee function of Definition 5. Then pure Nash equilibria of the $\eta$-subgame exist as follows.
--
--   1. If $\eta \le (N-1)b$:
--      - (a) if $c \in \big(\hat c(K_\eta+1),\ \phi bP_h + \hat c(K_\eta)\big]$, some pure profile in which exactly $K_\eta$ funds engage is a Nash equilibrium;
--      - (b) for every $L_\eta \in \{K_\eta+1,\dots,N-1\}$, if $c \in \big(\hat c(L_\eta+1),\ \hat c(L_\eta)\big]$, some pure profile in which exactly $L_\eta$ funds engage is a Nash equilibrium;
--      - (c) if $c \le \hat c(N)$, the profile in which all $N$ skilled funds engage is a Nash equilibrium.
--   2. If $\eta \in ((N-1)b, \alpha]$ and $c \le \phi bP_h + \hat c(N)$, the profile in which all $N$ skilled funds engage is a Nash equilibrium.
--
--   $$\text{(1a)}\quad \hat c(K_\eta+1) < c \le \phi bP_h + \hat c(K_\eta) \ \Longrightarrow\ \exists\ \text{a pure equilibrium with } K_\eta \text{ engagers}.$$
--
--   Since $\hat c$ is strictly decreasing, the intervals of part 1 tile the half-line $c \le \phi bP_h + \hat c(K_\eta)$; this is what lets Proposition 4 select a successful pure equilibrium for every such cost.
--
--   **Formalization Note.** Part 1(c) is printed with the strict inequality $c < \hat c(N)$. The proof (p. A6) establishes $c \le \hat c(N)$, and Proposition 4 needs the endpoint $c = \hat c(N)$, which the printed intervals miss; the statement uses $\le$, a strengthening that the printed proof proves. Actions are `Bool` with `true` = engage; $(N-1)b$ is computed in the reals.
-- source:
--   Brav, Dasgupta & Mathews, Wolf Pack Activism, accepted manuscript (May 2021, LSE eprint 112118 / SSRN 2529230), p. 19 (PDF 20), Lemma 2; proof pp. A3–A6 (PDF 38–41)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WolfPack.FlowEngage

/-- **Lemma 2** (p. 19), subgame equilibria of the delegated game with competition
for flow, for `η ∈ (b, α]`. Actions are `Bool`, with `true` = engage. Part 1(c) is
stated with `c ≤ ĉ(N)` (the printed lemma has `c < ĉ(N)`; its proof, p. A6, shows
`c ≤ ĉ(N)`, and Proposition 4 needs the endpoint).
1. If `η ≤ (N − 1) b`:
   (a) for `c ∈ (ĉ(Kη + 1), φ b Ph + ĉ(Kη)]` some pure profile with exactly `Kη`
       engagers is a Nash equilibrium of the `η`-subgame;
   (b) for `Lη ∈ {Kη + 1, …, N − 1}` and `c ∈ (ĉ(Lη + 1), ĉ(Lη)]` some pure profile
       with exactly `Lη` engagers is a Nash equilibrium;
   (c) for `c ≤ ĉ(N)` the profile in which all `N` skilled funds engage is a Nash
       equilibrium.
2. If `η ∈ ((N − 1) b, α]` and `c ≤ φ b Ph + ĉ(N)`, the profile in which all `N`
   skilled funds engage is a Nash equilibrium. -/
theorem lemma_2 (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p)) : (eta ≤ ((p.N : ℝ) - 1) * p.b → (p.c ∈ Set.Ioc (chat p (Keta p eta + 1)) (p.phi * p.b * p.Ph + chat p (Keta p eta)) → ∃ s : Fin p.N → Bool, numEngaged s = Keta p eta ∧ AGT.IsPureNash (subgamePayoff p eta .flow) s) ∧ (∀ L : ℕ, Keta p eta + 1 ≤ L → L ≤ p.N - 1 → p.c ∈ Set.Ioc (chat p (L + 1)) (chat p L) → ∃ s : Fin p.N → Bool, numEngaged s = L ∧ AGT.IsPureNash (subgamePayoff p eta .flow) s) ∧ (p.c ≤ chat p p.N → ∃ s : Fin p.N → Bool, numEngaged s = p.N ∧ AGT.IsPureNash (subgamePayoff p eta .flow) s)) ∧ (((p.N : ℝ) - 1) * p.b < eta → p.c ≤ p.phi * p.b * p.Ph + chat p p.N → ∃ s : Fin p.N → Bool, numEngaged s = p.N ∧ AGT.IsPureNash (subgamePayoff p eta .flow) s) := by sorry

end WolfPack.FlowEngage
