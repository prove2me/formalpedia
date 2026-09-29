-- Prove2me | Theorems.Thm_KServer_wfaU_potential_criterion_univ
-- name    : KServer.wfaU_potential_criterion_univ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:01:11.622425+00:00
-- url     : https://prove2.me/theorems/d7b6d5bb-5f03-41c5-a2dc-884c78f9a16f
-- title:
--   The potential-function criterion for the unlabelled WFA (universe-polymorphic)
-- statement:
--   Let $w_\tau$ denote the unlabelled work function of a $k$-server instance $(C_0, \tau)$ on a finite metric space $M$, and let $\mathrm{WFA}^u$ be the unlabelled Work Function Algorithm, which serves each request $s$ from configuration $C$ by moving to a configuration $C'$ containing $s$ that minimizes $\mathrm{mc}(C, C') + w_\tau(C')$. Suppose a potential $\Phi \colon M^* \to \mathbb{R}$ satisfies, for a constant $C \ge 0$:
--
--   **Offset property.** For every sequence $\tau$ and configuration $X$,
--   $$0 \;\le\; \Phi(\tau) + (C+1)\, w_\tau(X);$$
--
--   **Update property.** For every $\tau$, request $s$, and configuration $X$,
--   $$w_{\tau s}(X) \;\le\; w_\tau(X) + \bigl(\Phi(\tau) - \Phi(\tau s)\bigr).$$
--
--   Then $\mathrm{WFA}^u$ is $C$-competitive.
--
--   ## Role
--
--   This is the potential-function criterion of Bein, Chrobak and Larmore ('The 3-server problem in the plane', Lemma 3), adapted to the unlabelled work function: it reduces competitiveness of the work function algorithm to two purely analytic properties of a potential, and is the final step of the Coester--Koutsoupias $3$-competitiveness proof on trees, where $\Phi$ is built from their anchored potential.
--
--   ## Formalization note
--
--   This is the universe-polymorphic form of the previously proved `wfaU_potential_criterion`: the metric space `M` is `Type*` rather than `Type`, so the criterion can be applied to statements quantified over metric spaces in arbitrary universes. The statement is otherwise identical.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, 'The 3-server problem in the plane', ESA 1999 / TCS 289 (2002), Lemma 3, adapted to the unlabelled work function; universe-polymorphic restatement of wfaU_potential_criterion.

import Mathlib
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_wfaU

namespace KServer

theorem wfaU_potential_criterion_univ (k : ℕ) (hk : 0 < k) (M : Type*) [MetricSpace M]
    [Fintype M] (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFAU hk C₀) C := by sorry

end KServer
