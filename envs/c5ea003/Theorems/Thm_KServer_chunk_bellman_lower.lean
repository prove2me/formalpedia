-- Prove2me | Theorems.Thm_KServer_chunk_bellman_lower
-- name    : KServer.chunk_bellman_lower
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T03:04:14.247918+00:00
-- url     : https://prove2.me/theorems/4d22a8fd-db85-4b26-9a97-ba201e2090e6
-- title:
--   Bellman lower bound against every online evader and escape rule
-- statement:
--   Let X be a finite metric space and Ω a finite outcome space. Let Pω ≥ 0 be arbitrary, not necessarily normalized weights, and let σ(ω) be request sequences of length at most n whose requested sets are nonempty. Fix any real escape price p, any preceding history h, any deterministic online evader E, and any online bailout predicate b. The finite-horizon Bellman lower value satisfies
--
--   $$V_n(P,\sigma,E(h))\leq\sum_{\omega\in\Omega}P_\omega\,\mathrm{bailCost}_{E,b}(h,\sigma(\omega),p).$$
--
--   At each step V takes the minimum of escaping before the next request is revealed and continuing, branching on the next requested set and minimizing over the serving position within it. Empty remaining sequences contribute zero even when the bailout predicate is true. After branching, outcome weights are restricted without renormalization.
--
--   The bound certifies online conditional cost lower bounds for random chunks. Using unnormalized weights makes it applicable directly to filtration atoms, including outcomes given weight zero. The statement is a lower bound and does not claim an optimal policy is attained.
-- source:
--   Derived Bellman soundness lemma for the online conditional cost inequalities of Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4, Lemma 12 and Lemma 15, equation (6), printed pp. 14 and 19–21. Its escape timing is exactly the platform EvaderAlgorithm.bailCost definition. The dynamic-programming bound is independently proved formalization infrastructure, not a verbatim theorem in the paper.

import Definitions.Def_KServer_chunk_bellman
open KServer

theorem KServer.chunk_bellman_lower {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) (n : ℕ) (P : Ω → ℝ)
    (σ : Ω → List (Set X)) (hP : ∀ ω, 0 ≤ P ω)
    (hlen : ∀ ω, (σ ω).length ≤ n)
    (hne : ∀ ω, ∀ S ∈ σ ω, S.Nonempty)
    (E : EvaderAlgorithm X) (b : List (Set X) → Bool) (h : List (Set X)) :
    chunkBellman p n P σ (E.pos h) ≤ ∑ ω, P ω * E.bailCost b h (σ ω) p := by sorry
