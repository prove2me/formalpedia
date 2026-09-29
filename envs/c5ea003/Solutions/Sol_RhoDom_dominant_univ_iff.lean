-- Prove2me | solution 1 for RhoDom.dominant_univ_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:58.120779+00:00
-- url     : https://prove2.me/submissions/e60273ec-3929-4049-ba95-72ac10aa978a

-- Sol generated from Geometry/RhoDominantCartan.lean
import Mathlib
import Definitions.Def_Geometry_RhoDominantCartan

/-!
# ρ-dominant weights `λ_{D,I}` in the simply-laced case: a degree criterion

## Mission context

The research target concerns the classification of **ρ-dominant elements** of the crystal
`B(ρ)` of the irreducible integrable highest-weight module `L(ρ)` of a symmetrizable
Kac–Moody algebra.  Every such element is claimed to arise as a `π_{D,I}`, built from

* a subgraph `I` of the Dynkin diagram with only **simple bonds** and **no cycle of length
  `≥ 3`** (equivalently, `I` is a *simply-laced forest*),
* a subset `D ⊆ I`, subject to the condition that the weight
  `λ_{D,I} = 2ρ - β_I - β_D` is **dominant**, and
* a choice of a root vertex in each connected component of `I`.

A full formalization of crystals over Kac–Moody algebras is beyond current libraries.  What we
*can* isolate and prove rigorously is the **weight-theoretic backbone** of the construction: the
dominance condition `λ_{D,I} ∈ P⁺`.  In the simply-laced setting the generalized Cartan matrix
is `A = 2·Id − Adj(G)` for a simple graph `G`, and `⟨ρ, α_iᵛ⟩ = 1` for every simple coroot.
Writing `β_S = Σ_{j∈S} α_j`, the pairing `⟨β_S, α_iᵛ⟩` becomes a purely graph-theoretic
quantity, and dominance of `λ_{D,I}` turns into a clean inequality on vertex degrees.

## Main results

* `RhoDom.betaPair_mem` / `RhoDom.betaPair_notmem` : closed forms for `⟨β_S, α_iᵛ⟩`.
* `RhoDom.dominant_univ_iff` : with `I` the whole (simply-laced) diagram, `λ_{D,I}` is dominant
  **iff** every vertex `i ∈ D` satisfies `deg i + deg_D i ≥ 2`.
* `RhoDom.dominant_singleton_iff` : a *singleton* `D = {v}` yields a dominant weight iff
  `deg v ≥ 2`; in particular a leaf can never carry a dominant singleton.
* `RhoDom.dominant_empty`, `RhoDom.dominant_of_min_degree` : sufficient conditions.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The abstract dominance condition `λ_{D,I} = 2ρ − β_I − β_D ∈ P⁺`,
  which sits at the heart of the `π_{D,I}` classification, is — in the simply-laced case —
  equivalent to a local combinatorial inequality on the Dynkin graph, namely a lower bound on
  `deg i + deg_D i` for the marked vertices `i ∈ D`.
Experiment (Experimenter): Modelled the simply-laced GCM as `A = 2·Id − Adj(G)`.  Proved the
  pairing formulas `⟨β_S, α_iᵛ⟩ = 2 − deg_S i` (for `i ∈ S`) and `= −deg_S i` (for `i ∉ S`) by
  splitting the coroot sum at the diagonal term and using irreflexivity of `G`.  Feeding these
  into `2 − ⟨β_I,·⟩ − ⟨β_D,·⟩` collapsed the whole-diagram case to `deg i + deg_D i ≥ 2`.
Analysis (Analyst): The `i ∉ D` half of the criterion is *automatic* (`deg i + deg_D i ≥ 0`),
  so dominance is governed entirely by the marked set `D`.  This matches the paper's intuition
  that `D` records "where the extra `−β_D` correction risks pushing a coordinate negative".
Critique (Critic): The theorem is the honest simply-laced specialization; it does not assert the
  full crystal classification (crystals are not yet formalizable here) and does not silently
  assume `I` is a forest — `dominant_univ_iff` holds for an arbitrary simple graph, and the
  forest hypothesis only enters the *companion* structural results (see `RhoDominantForest`).
Synthesis (PI): `dominant_univ_iff` is the reusable engine; `dominant_singleton_iff` is the
  crisp leaf obstruction that the forest file consumes.
-- !-- Lab Notes -- !--
-/

open Finset

open RhoDom

variable {n : ℕ}




/-- Over `S.erase i` the coroot sum is exactly `-deg_S i`, because the diagonal term is removed
and off-diagonal entries are `-1` precisely on edges. -/
theorem sum_erase_cartan (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (i : Fin n) :
    ∑ x ∈ S.erase i, cartan G i x = - (degIn G S i : ℤ) := by
  unfold degIn
  rw [Finset.card_filter]
  push_cast
  have hi0 : (if G.Adj i i then (1 : ℤ) else 0) = 0 := by simp
  rw [← Finset.sum_erase S hi0, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hxi : x ≠ i := (Finset.mem_erase.1 hx).1
  simp only [cartan, if_neg (Ne.symm hxi)]
  by_cases h : G.Adj i x <;> simp [h]

/-- Closed form for the coroot pairing when `i ∈ S`: `⟨β_S, α_iᵛ⟩ = 2 − deg_S i`. -/
theorem betaPair_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    betaPair G S i = 2 - (degIn G S i : ℤ) := by
  unfold betaPair
  rw [← Finset.add_sum_erase S (cartan G i) hi, sum_erase_cartan]
  have : cartan G i i = 2 := by simp [cartan]
  rw [this]; ring

/-- Closed form for the coroot pairing when `i ∉ S`: `⟨β_S, α_iᵛ⟩ = −deg_S i`. -/
theorem betaPair_notmem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    betaPair G S i = - (degIn G S i : ℤ) := by
  unfold betaPair
  rw [← Finset.erase_eq_of_notMem hi, sum_erase_cartan, Finset.erase_eq_of_notMem hi]




/-- Taking `S = univ` recovers the ordinary graph degree. -/
theorem degIn_univ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    degIn G Finset.univ i = G.degree i := by
  unfold degIn
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]







open RhoDom in
theorem solution(G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :
    IsRhoDominant G Finset.univ D ↔ ∀ i ∈ D, 2 ≤ G.degree i + degIn G D i := by
  unfold IsRhoDominant rhoDomPair
  constructor
  · intro h i hiD
    have hi := h i
    rw [betaPair_mem G Finset.univ i (Finset.mem_univ i), betaPair_mem G D i hiD, degIn_univ] at hi
    omega
  · intro h i
    rw [betaPair_mem G Finset.univ i (Finset.mem_univ i), degIn_univ]
    by_cases hiD : i ∈ D
    · rw [betaPair_mem G D i hiD]; have := h i hiD; omega
    · rw [betaPair_notmem G D i hiD]; omega
