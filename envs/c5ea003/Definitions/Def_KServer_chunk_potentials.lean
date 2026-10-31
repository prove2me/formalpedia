-- Prove2me | Definitions.Def_KServer_chunk_potentials
-- name    : KServer_chunk_potentials
-- status  : Definition
-- author  : @kwal0203
-- created : 2026-10-30T06:13:06.154539+00:00
-- url     : https://prove2.me/theorems/8ffdb22a-15c3-4d7d-a8e9-bd43516730c1
-- title:
--   Local linear potential certificates for chunk Bellman bounds
-- statement:
--   Fix a finite metric space X, a finite outcome space Ω, request sequences σ, weights P, an escape price p, and a horizon n. A local potential certificate for a function v:X→ℝ is a finite-depth collection of linear inequalities below the chunk Bellman recursion.
--
--   At horizon zero the condition is v(x) ≤ 0. At a successor horizon, write Pₛ for weights restricted to outcomes whose next request is S and μₛ for their total mass. Choose branch values zₛ(x) and recursively certified continuation potentials uₛ(y), with
--
--   $$v(x)\le p\sum_{\omega:\sigma(\omega)\ne[]}P_\omega,\qquad v(x)\le\sum_S z_S(x),$$
--
--   $$z_S(x)\le\mu_S d(x,y)+u_S(y)\qquad(\varnothing\ne S,\ y\in S).$$
--
--   For the empty request-set branch require zₛ(x) ≤ 0. Each continuation is certified at horizon n−1 for Pₛ and the tails of σ. No minimization occurs in these constraints. For fixed probabilities, metric data and request sequences, the expanded certificate consists of finitely many linear inequalities in finitely many real potential variables.
--
--   The module also defines a chunk-system package whose cost constraints are certified by such potentials on each filtration atom. All probability, filtration, request, horizon, size-window, count, terminal-request, offline-cost and total-mass requirements are retained. The potential must dominate the desired size certificate at positions compatible with the known preceding request history. This interface does not assert that a regrouping construction exists.
-- source:
--   Local-subsolution formalization of the platform KServer.chunkBellman recursion and the online conditional-cost requirement of Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.3, Lemma 15, equation (6), printed pp. 19–21. The local linear potential interface is explicitly derived proof infrastructure rather than a verbatim definition in the paper.

import Definitions.Def_KServer_chunk_bellman

namespace KServer

/-- A finite tree of local linear inequalities certifying a Bellman lower value. -/
def IsChunkPotential {X : Type*} [MetricSpace X] [Fintype X]
    {Ω : Type*} [Fintype Ω] (p : ℝ) :
    ℕ → (Ω → ℝ) → (Ω → List (Set X)) → (X → ℝ) → Prop
  | 0, _, _, v => ∀ x, v x ≤ 0
  | n + 1, P, σ, v => by
    classical
    exact ∃ (z u : Set X → X → ℝ),
      (∀ S : Set X, IsChunkPotential p n
        (fun ω => if (σ ω).head? = some S then P ω else 0)
        (fun ω => (σ ω).tail) (u S)) ∧
      (∀ x, v x ≤ p * ∑ ω, if σ ω = [] then 0 else P ω) ∧
      (∀ x, v x ≤ ∑ S : Set X, z S x) ∧
      (∀ S : Set X, ¬ S.Nonempty → ∀ x, z S x ≤ 0) ∧
      (∀ (S : Set X), S.Nonempty → ∀ (x y : X), y ∈ S →
        z S x ≤ (∑ ω, if (σ ω).head? = some S then P ω else 0) * dist x y + u S y)

structure PotentialChunkSystemB (X : Type*) [MetricSpace X] [Fintype X] (s t : X)
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
  hcost : ∀ (i : Fin m) (ω₀ : Ω), ∃ v : X → ℝ,
    IsChunkPotential price H (fun ω => if hist i ω = hist i ω₀ then P ω else 0)
      (fun ω => chunk ω i) v ∧
    ∀ x, PositionAllowed (((List.ofFn (chunk ω₀)).take i).flatten) x →
      size ω₀ i * (∑ ω ∈ Finset.univ.filter (fun ω => hist i ω = hist i ω₀), P ω) ≤ v x
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)



attribute [instance] PotentialChunkSystemB.instFin PotentialChunkSystemB.instDec

end KServer


