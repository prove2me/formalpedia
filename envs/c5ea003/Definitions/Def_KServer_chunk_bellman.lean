-- Prove2me | Definitions.Def_KServer_chunk_bellman
-- name    : KServer_chunk_bellman
-- status  : Definition
-- author  : @kwal0203
-- created : 2026-10-30T03:02:32.631173+00:00
-- url     : https://prove2.me/theorems/0d3ad1cb-ec7b-4fb0-b164-ef956a8fc259
-- title:
--   Bellman lower values for random chunks with online escape
-- statement:
--   Let X be a finite metric space, Ω a finite outcome space, P nonnegative outcome weights, σ(ω) a finite request sequence, and p an escape price. No normalization of P is built into the definition. For each possible first request S, let Pₛ be P restricted to outcomes whose sequence starts with S, and let μₛ be its total mass.
--
--   The finite-horizon Bellman lower value is defined by V₀=0 and
--
--   $$V_{n+1}(P,\sigma,x)=\min\left\{p\sum_{\omega:\sigma(\omega)\ne[]}P_\omega,\quad\sum_{\varnothing\ne S\subseteq X}\min_{y\in S}\left[\mu_S d(x,y)+V_n(P_S,\operatorname{tail}\sigma,y)\right]\right\}.$$
--
--   The escape decision is made before revealing the next request. If the policy continues, it may choose a new position y after seeing S. Outcomes whose chunk has already ended incur no further cost, including no escape payment. The soundness theorem uses nonempty requested sets and a horizon at least the length of every sampled chunk.
--
--   The module also supplies a Bellman-certified chunk-system structure. It retains the probabilities, refining filtration, adapted sizes, size window, count and expected-total bounds, feasible requests, terminal request, offline-cost bound, and common request horizon of the finite-horizon certificate interface. On each filtration atom A, its cost condition is the numerical inequality
--
--   $$c_i(\omega_0)P(A)\le V_H(P\mathbf1_A,\chi_i,x)$$
--
--   for each current position x compatible with the latest request in the known preceding history. For an empty history every position is compatible. This replaces universal policy-table tests by sufficient recursive lower-value bounds; it does not assert that such a construction exists for arbitrary parameters.
-- source:
--   Derived dynamic-programming formalization of Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4, Lemma 12 and Lemma 15, equation (6), printed pp. 14 and 19–21. The underlying online escape timing follows the platform EvaderAlgorithm.bailCost definition. The Bellman recursion and legal-position certificate are explicitly introduced proof infrastructure, not a verbatim definition in the paper.

import Definitions.Def_KServer_finite_chunk_certificates

namespace KServer

/-- Unnormalised finite-horizon Bellman lower value for a random request chunk.
The first branch is online escape before seeing the next request. -/
noncomputable def chunkBellman {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) :
    ℕ → (Ω → ℝ) → (Ω → List (Set X)) → X → ℝ
  | 0, _, _, _ => 0
  | n + 1, P, σ, x => by
    classical
    exact min (p * ∑ ω, if σ ω = [] then 0 else P ω)
      (∑ S : Set X, if hS : S.Nonempty then
        (Finset.univ.filter (fun y : X => y ∈ S)).inf'
          (by obtain ⟨y, hy⟩ := hS; exact ⟨y, by simp [hy]⟩)
          (fun y => (∑ ω, if (σ ω).head? = some S then P ω else 0) * dist x y +
            chunkBellman p n (fun ω => if (σ ω).head? = some S then P ω else 0)
              (fun ω => (σ ω).tail) y)
        else 0)


/-- Positions compatible with the latest request of a known history. -/
def PositionAllowed {X : Type*} (h : List (Set X)) (x : X) : Prop :=
  ∀ (l : List (Set X)) (S : Set X), h = l ++ [S] → S.Nonempty → x ∈ S

/-- A chunk certificate verified by numerical Bellman lower bounds on each atom. -/
structure BellmanChunkSystemB (X : Type*) [MetricSpace X] [Fintype X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  P : Ω → ℝ
  m : ℕ
  H : ℕ
  hist : ℕ → Ω → ℕ
  chunk : Ω → Fin m → List (Set X)
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 < P ω
  hPsum : ∑ ω, P ω = 1
  hm : mLo ≤ m
  hm0 : 0 < m
  href : ∀ i j : ℕ, i ≤ j → ∀ ω ω', hist j ω = hist j ω' → hist i ω = hist i ω'
  hadapt : ∀ (i : Fin m) (ω ω' : Ω), hist (i + 1) ω = hist (i + 1) ω' →
    chunk ω i = chunk ω' i
  hsmeas : ∀ (i : Fin m) (ω ω' : Ω), hist i ω = hist i ω' → size ω i = size ω' i
  hne : ∀ ω i, ∀ S ∈ chunk ω i, S.Nonempty
  hlast : ∀ ω, (((List.ofFn (chunk ω)).flatten).getLast?) = some {t}
  hopt : ∀ ω, evaderOfflineCost s ((List.ofFn (chunk ω)).flatten) ≤ dist s t
  hsize : ∀ ω i, cLo ≤ size ω i ∧ size ω i ≤ cHi
  hH : ∀ ω, ((List.ofFn (chunk ω)).flatten).length ≤ H
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (x : X),
    PositionAllowed (((List.ofFn (chunk ω₀)).take i).flatten) x →
    size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω)
      ≤ chunkBellman price H (fun ω => if hist i ω = hist i ω₀ then P ω else 0)
          (fun ω => chunk ω i) x
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)


attribute [instance] BellmanChunkSystemB.instFin BellmanChunkSystemB.instDec

end KServer


