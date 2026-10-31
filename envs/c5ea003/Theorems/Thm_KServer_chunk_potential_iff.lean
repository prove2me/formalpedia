-- Prove2me | Theorems.Thm_KServer_chunk_potential_iff
-- name    : KServer.chunk_potential_iff
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T06:16:08.285945+00:00
-- url     : https://prove2.me/theorems/5ea30aa7-ca6f-41b0-b6fd-2ddf6adcbb5a
-- title:
--   Exact local potential certificates for Bellman lower bounds
-- statement:
--   Let X and Ω be finite, with a metric on X. Fix an escape price p, horizon n, real weights P on Ω, request sequences σ, and a function v:X→ℝ. The local potential conditions characterize Bellman lower bounds exactly:
--
--   $$\mathrm{IsChunkPotential}(p,n,P,\sigma,v)\quad\Longleftrightarrow\quad\forall x\in X,\ v(x)\le V_n(P,\sigma,x).$$
--
--   The local conditions use an escape bound, branch lower values, movement inequalities for every legal serving position, recursively certified continuation potentials, and terminal inequalities at depth zero. For fixed metric, weights and requests, the expanded conditions are finite linear inequalities in real potential variables; they contain no nested minima.
--
--   The characterization is algebraic and requires no sign or normalization condition on P. When the weights, requests and horizon satisfy the hypotheses of the online Bellman lower-bound theorem, any such potential is consequently a valid online cost lower bound. The equivalence does not supply a regrouping distribution or claim an efficient algorithm for searching all possible distributions.
-- source:
--   Derived local-subsolution characterization of the platform KServer.chunkBellman recursion. Application context: Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.3, Lemma 15, equation (6), printed pp. 19–21. This exact finite-potential characterization is independently proved formalization infrastructure, not a verbatim theorem of the paper.

import Definitions.Def_KServer_chunk_potentials
open KServer

theorem KServer.chunk_potential_iff {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) (n : ℕ) (P : Ω → ℝ)
    (σ : Ω → List (Set X)) (v : X → ℝ) :
    IsChunkPotential p n P σ v ↔ ∀ x, v x ≤ chunkBellman p n P σ x := by sorry
