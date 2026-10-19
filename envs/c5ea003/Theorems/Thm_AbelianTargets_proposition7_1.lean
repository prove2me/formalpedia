-- Prove2me | Theorems.Thm_AbelianTargets_proposition7_1
-- name    : AbelianTargets.proposition7_1
-- status  : Proved
-- author  : @username
-- created : 2026-10-18T07:42:42.502744+00:00
-- url     : https://prove2.me/theorems/3e50f7bf-ffa5-4106-a484-09a1054bd56e
-- title:
--   Proposition 7.1 — continuous homomorphisms for lattice actions
-- statement:
--   Let $H$ be a finite simple graph with discrete vertex set $V$. Suppose $H$ contains an odd closed walk $\gamma$ whose reduced class has finite order, meaning $[\gamma]^N=1$ for some integer $N>0$ in the reduced homotopy group $\Pi_1^*(H,b)$ at its base vertex $b$. Then for every integer $d\geq1$, every free continuous $\mathbb Z^d$-action on every zero-dimensional Polish space $X$ admits a continuous graph homomorphism from its standard Schreier graph to $H$. Equivalently,
--
--   $$
--   \exists N>0,\ [\gamma]^N=1\quad\Longrightarrow\quad \forall d\geq1,\ \operatorname{UniversalTarget}(d,H).
--   $$
--
--   Here the standard Schreier graph joins $x$ to $e_i\cdot x$, and reduced homotopy permits spur and closed four-walk cancellations. No connectedness assumption is made on $H$. The result provides one finite target for all the specified actions in every positive dimension.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Proposition 7.1; https://arxiv.org/html/2609.39824v1#S7.SS1. Lean proof source: AbelianTargets/PositiveTheorems.lean, lines 53-62, SHA-256 72f36f05675ae84f52f933d00ea9df29391a52807814b57263eb081d5b1a0fc6. Original local project: arxiv-2609-39824-lean. No public source repository URL or commit was available; source identity is recorded by content hash and original file locator.

import Definitions.Def_AbelianTargets260939824Actions
import Definitions.Def_AbelianTargets260939824ReducedWalks

set_option autoImplicit false

universe u v

theorem AbelianTargets.proposition7_1
    {V : Type v} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) :
    AbelianTargets.HasOddTorsion H → ∀ d : ℕ, 1 ≤ d →
      AbelianTargets.UniversalTarget.{u} d H := by sorry
