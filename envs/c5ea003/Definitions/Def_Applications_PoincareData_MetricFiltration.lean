-- Prove2me | Definitions.Def_Applications_PoincareData_MetricFiltration
-- name    : Applications_PoincareData_MetricFiltration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:30:41.281635+00:00
-- url     : https://prove2.me/theorems/d1d27ab7-5d29-49b1-b529-37be1ad5cb57
-- title:
--   Aether Catalog definitions — Applications_PoincareData_MetricFiltration
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PoincareData.MetricFiltration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PoincareData/MetricFiltration.lean by skeleton subtraction
import Mathlib
/-
  # Metric Filtrations and Rips Graphs

  This file introduces the **RipsGraph** construction and the **MetricFiltration** structure,
  formalizing the scale-dependent graph filtration that underlies persistent homology and
  topological data analysis. The Rips graph at scale ε connects points within distance ε;
  as ε grows, the graph grows monotonically, yielding a filtration of SimpleGraphs.

  ## Novel Structure: MetricFiltration

  A `MetricFiltration` is a monotone family of SimpleGraphs indexed by ℝ, together with
  boundary conditions (trivial at negative scale). This captures the π₀-level behavior
  of the Vietoris-Rips complex and provides the algebraic foundation for the "Poincaré
  threshold" — the critical scale at which a point cloud's connectivity matches that of
  a target manifold.

  ## Main Results

  * `ripsGraph` — the Rips graph at scale ε for a pseudometric space
  * `ripsGraph_mono` — filtration monotonicity (PEGB Theorem 1)
  * `ripsGraph_bot_of_metric` — boundary: empty at scale 0 in metric spaces
  * `ripsGraph_bot_of_neg` — boundary: empty at negative scale
  * `coveringNumber_antitone` — covering number decreases with scale (PEGB Theorem 2)
  * `sphere_perturbation_stability` — robustness of sphere detection (PEGB Theorem 3)
  * `sphere_diam_bound` — diameter bound for spherical point clouds (PEGB Theorem 4)
  * `maximal_packing_is_cover` — packing-covering duality (PEGB Theorem 5)
-/

open Finset Set

noncomputable section

/-! ## Part 1: Rips Graph Construction -/

/-- The **Rips graph** (also called Vietoris-Rips 1-skeleton) of a pseudometric space
    at scale ε. Two distinct vertices are adjacent iff their distance is at most ε. -/
def ripsGraph (α : Type*) [PseudoMetricSpace α] (ε : ℝ) : SimpleGraph α where
  Adj x y := x ≠ y ∧ dist x y ≤ ε
  symm x y h := ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-! ## Part 2: PEGB Theorem 1 — Filtration Monotonicity -/

-- !-- **Proof**: If ε₁ ≤ ε₂ and dist(x,y) ≤ ε₁, then dist(x,y) ≤ ε₂ by transitivity.
-- **Example**: ripsGraph ℝ 1 ≤ ripsGraph ℝ 2.
-- **Generalization**: Works for any pseudometric space, not just ℝ^d.
-- **Boundary**: At ε = 0 in a metric space, the graph is empty (ripsGraph_bot_of_metric). -- !--

-- Boundary: at scale 0 in a metric space, the graph is empty

-- Boundary: at negative scale, the graph is empty

-- Example
/-! ## Part 3: The MetricFiltration Structure -/

/-- A **MetricFiltration** on a type α is a monotone family of SimpleGraphs
    parameterized by a real-valued scale, together with boundary behavior.
    This abstracts the Rips construction and captures any scale-dependent
    graph filtration arising from geometric or topological considerations.

    This is a novel mathematical structure that provides the algebraic skeleton
    for persistent homology computations without requiring the full simplicial
    complex machinery. -/
structure MetricFiltration (α : Type*) where
  /-- The graph at scale ε -/
  graphAt : ℝ → SimpleGraph α
  /-- Monotonicity: larger scale ⟹ more edges -/
  mono : Monotone graphAt
  /-- At sufficiently negative scale, the graph is trivial -/
  trivial_at_neg : ∀ ε < 0, graphAt ε = ⊥




/-! ## Part 4: Covering Numbers -/

/-- An **ε-cover** of a finset S is a finset C such that every point of S
    is within distance ε of some point of C. -/
def IsEpsilonCover {α : Type*} [PseudoMetricSpace α]
    (S C : Finset α) (ε : ℝ) : Prop :=
  ∀ x ∈ S, ∃ c ∈ C, dist x c ≤ ε

/-- An **ε-packing** of a finset S is a finset P ⊆ S such that all distinct
    pairs in P have distance > ε. -/
def IsEpsilonPacking {α : Type*} [PseudoMetricSpace α]
    (S P : Finset α) (ε : ℝ) : Prop :=
  P ⊆ S ∧ ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ε < dist x y

/-- The **covering number** N(S, ε) is the minimum cardinality of an ε-cover. -/
def coveringNumber {α : Type*} [PseudoMetricSpace α]
    (S : Finset α) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset α, C.card = k ∧ IsEpsilonCover S C ε}




/-! ## Part 5: PEGB Theorem 2 — Covering Number Antitone -/

-- !-- **Proof**: If ε₁ ≤ ε₂, then every ε₁-cover is an ε₂-cover (isEpsilonCover_mono),
-- so the set of achievable cardinalities for ε₂ contains that for ε₁. The infimum
-- of a larger set is ≤ the infimum of a smaller set.
-- **Example**: On {0,1,2} ⊂ ℝ, N(0.5) = 3 but N(1.5) ≤ 2.
-- **Generalization**: Holds for any pseudometric space, finite or infinite (via Finset).
-- **Boundary**: coveringNumber_empty shows N(∅, ε) = 0 for all ε. -- !--

-- Boundary: covering number of empty set is 0

-- Boundary: covering number of a singleton ≤ 1

/-! ## Part 6: PEGB Theorem 3 — Sphere Perturbation Stability -/

/-- Points on a sphere: every point has distance r from center c. -/
def LiesOnSphere {n d : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Prop :=
  ∀ i : Fin n, dist (X i) c = r

/-- Points approximately on a sphere: distance to center is within δ of r. -/
def LiesApproxOnSphere {n d : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r δ : ℝ) : Prop :=
  ∀ i : Fin n, |dist (X i) c - r| ≤ δ

/-
!-- **Proof**: For each point Y_i, by triangle inequality
|dist(Y_i, c) - r| = |dist(Y_i, c) - dist(X_i, c)| ≤ dist(X_i, Y_i) ≤ δ.
The key step uses |dist(a,c) - dist(b,c)| ≤ dist(a,b).
**Example**: If X lies on the unit circle and Y is a 0.01-perturbation,
then Y lies within 0.01 of the unit circle.
**Generalization**: Works in any dimension d and for any center/radius.
**Boundary**: When δ = 0, LiesApproxOnSphere reduces to LiesOnSphere. -- !--
-/

/-! ## Part 7: PEGB Theorem 4 — Sphere Diameter Bound -/

/-
!-- **Proof**: For any i,j on the sphere of radius r centered at c,
dist(X_i, X_j) ≤ dist(X_i, c) + dist(c, X_j) = r + r = 2r
by triangle inequality.
**Example**: Points on the unit circle in ℝ² have pairwise distance ≤ 2.
**Generalization**: Works in any pseudometric space, not just Euclidean.
**Boundary**: The bound 2r is tight (antipodal points achieve it). -- !--
-/

/-! ## Part 8: PEGB Theorem 5 — Packing-Covering Duality -/

/-
!-- **Proof**: For x ∈ P, we have dist(x,x) = 0 ≤ ε. For x ∈ S \ P,
maximality gives p ∈ P with dist(x,p) ≤ ε. So P is an ε-cover of S.
**Example**: On {0, 1, 2, 3} with ε = 1, {0, 2} is a maximal 1-packing
and also a 1-cover.
**Generalization**: This is the fundamental packing-covering duality in
metric geometry; it underpins the n^{-1/d} scaling of the Poincaré threshold.
**Boundary**: For ε < 0, no nontrivial packing/cover exists. -- !--
-/

/-! ## Part 9: Complete Graph Threshold -/

-- The complete graph on a nonempty finite type is connected.

/-! ## Part 10: Cross-connection to existing catalog -/

-- Cross-connection: The Rips filtration's monotonicity connects to the simplicial
-- complex monotonicity in SimplicialComplex.lean. Here we show the graph-level
-- monotonicity implies a supergraph relationship.

/-- Two MetricFiltrations can be compared pointwise. This partial order on
    filtrations connects to the simplicial order on complexes. -/
instance {α : Type*} : LE (MetricFiltration α) where
  le F G := ∀ ε, F.graphAt ε ≤ G.graphAt ε


/-! ## Part 11: Additional Examples and Boundary Cases -/

-- Example: Self-cover
-- Example: Monotonicity chain
-- Transitivity
-- Boundary: the Rips filtration gives the bottom graph for all negative ε

end


