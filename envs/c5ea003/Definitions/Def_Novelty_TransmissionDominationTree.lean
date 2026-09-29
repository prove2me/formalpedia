-- Prove2me | Definitions.Def_Novelty_TransmissionDominationTree
-- name    : Novelty_TransmissionDominationTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T21:19:55.165191+00:00
-- url     : https://prove2.me/theorems/8a6e5b83-c226-4ebb-b0f4-56c0cec7a57a
-- title:
--   Aether Catalog definitions — Novelty_TransmissionDominationTree
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TransmissionDominationTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TransmissionDominationTree.lean by skeleton subtraction
import Mathlib

/-!
# Domination number of paths (and the transmission–zero-forcing / domination program)

This file is the first research cycle on the direction

> *Transmission Zero Forcing Number Equals Domination Number on Trees.*

The deepest *fully verified* contribution here is an exact, closed-form evaluation of the
**domination number of the path graph** `P_n` (which is the simplest infinite family of
trees):

  `γ(P_n) = ⌈n/3⌉ = (n + 2) / 3`   (natural-number division).

We give two equivalent developments and connect them:

* a self-contained **combinatorial** model `DominatesPath` / `gammaPath` on `ℕ`, where the
  domination number of `P_n` is computed exactly (`gammaPath_eq`);
* a **genuine graph-theoretic** definition `IsDominatingSet` / `dominationNumber` for an
  arbitrary `SimpleGraph`, together with a card-preserving bridge proving that the
  graph domination number of `Mathlib`'s `SimpleGraph.pathGraph n` equals the combinatorial
  `gammaPath n` (`dominationNumber_pathGraph`), hence equals `(n+2)/3`
  (`dominationNumber_pathGraph_eq`).

The `dominationNumber` definition is stated for general finite graphs so that future cycles
can reuse it for stars, caterpillars, spiders and general trees.

-- !-- Lab Notes -- !--
## Hypothesis
The mission conjecture is `ξ_T(T) = γ(T)` for every tree `T`, where `ξ_T` is a
"transmission zero forcing number".  Ordinary zero forcing fails this badly
(`Z(P_n) = 1` but `γ(P_n) = ⌈n/3⌉`), so any equality must use a *transmission-weighted*
variant.  The first scientific task is therefore to pin down `γ` itself exactly on the
canonical tree family, which is what this file does rigorously.

## Experimental outcome (see ComputationalEvidence.md)
Brute-force enumeration over `P_1 … P_9` confirms `γ(P_n) = ⌈n/3⌉ = 1,1,1,2,2,2,3,3,3`.
The same enumeration shows ordinary `Z(P_n) = 1` for all `n`, decisively separating ordinary
zero forcing from domination and motivating the "transmission" weighting in the conjecture.

## Insights
* The lower bound is a pure *closed-neighbourhood counting* argument: in a path every closed
  neighbourhood has at most `3` vertices, so a dominating set `S` satisfies `n ≤ 3·|S|`.
  This is exactly the `Δ`-degree bound `γ(G) ≥ n/(Δ+1)` specialised to `Δ = 2`, and it is the
  reusable kernel for the general tree program (`lower_bound`).
* The upper bound needs only the *existence* of a small dominating set, not its exact size:
  placing a guard at `min(3k+1, n-1)` for `k < ⌈n/3⌉` dominates everything, and
  `Finset.card_image_le` caps the cardinality without any injectivity bookkeeping
  (`dominates_construction`, `card_construction`).
* Encoding distance-≤1 as `i ≤ s+1 ∧ s ≤ i+1` over `ℕ` lets `omega` discharge every
  metric obligation, including the Euclidean-division case split `3k ≤ i ≤ 3k+2`.

## Failure analysis
* Working directly in `Fin n` makes the counting argument painful (wrap-around `s-1`,
  `Fin`-valued `Finset.Icc`).  Proving the value over `ℕ` and then *bridging* to
  `SimpleGraph.pathGraph` via `Finset.attachFin` / `Finset.image Fin.val` is dramatically
  cleaner and keeps `omega` in charge.
* `omega` does not reduce `(⟨i, hi⟩ : Fin n).val` to `i` by itself; an empty `simp only []`
  (projection reduction) before `omega` is load-bearing in the bridge lemmas.
-/

open Finset SimpleGraph

/-! ## Combinatorial model of domination on the path `P_n` -/

/-- `DominatesPath n S`: the finite set `S ⊆ {0,…,n-1}` is a dominating set of the path
graph `P_n`, i.e. every vertex `i < n` is within graph distance `≤ 1` of some `s ∈ S`
(distance `≤ 1` over `ℕ` is `i ≤ s + 1 ∧ s ≤ i + 1`). -/
def DominatesPath (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧ ∀ i ∈ Finset.range n, ∃ s ∈ S, i ≤ s + 1 ∧ s ≤ i + 1

/-- The (combinatorial) domination number of the path `P_n`. -/
noncomputable def gammaPath (n : ℕ) : ℕ :=
  sInf {k | ∃ S, DominatesPath n S ∧ S.card = k}

/-- The closed neighbourhood `{s-1, s, s+1}` of a path vertex, used for the counting bound. -/
def blockP (s : ℕ) : Finset ℕ := Finset.Icc (s - 1) (s + 1)

/-- A small dominating set: a guard at `min(3k+1, n-1)` for each `k < ⌈n/3⌉`. -/
noncomputable def domConstruction (n : ℕ) : Finset ℕ :=
  (Finset.range ((n + 2) / 3)).image (fun k => min (3 * k + 1) (n - 1))






/-! ## Genuine graph-theoretic domination number, and the bridge to `pathGraph` -/

/-- `D` is a dominating set of `G`: every vertex is in `D` or adjacent to a member of `D`. -/
def IsDominatingSet {V} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ d ∈ D, G.Adj d v

/-- The domination number of a finite graph: the least size of a dominating set. -/
noncomputable def dominationNumber {V} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, IsDominatingSet G D ∧ D.card = k}


