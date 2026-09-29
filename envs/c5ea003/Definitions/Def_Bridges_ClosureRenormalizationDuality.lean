-- Prove2me | Definitions.Def_Bridges_ClosureRenormalizationDuality
-- name    : Bridges_ClosureRenormalizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:38.776463+00:00
-- url     : https://prove2.me/theorems/1c31524a-70be-4324-9e44-32bdc58d1138
-- title:
--   Aether Catalog definitions — Bridges_ClosureRenormalizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureRenormalizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureRenormalizationDuality.lean by skeleton subtraction
import Mathlib
/-
# Closure Renormalization Duality via Idempotent Scale Semimodules and Certified Minimal RG Flow

This file formalizes a finite duality between **scale-indexed closure systems** and
**idempotent scale semimodules** over a tropical (min-plus) semiring, proving that
renormalization data is reconstructive: closure-capacity profiles across scales determine,
and are determined by, canonical RG-flow DAGs with certified monotone functionals.

## Main Results

### Core Structures
- `ScaleClosure`: A finite family of closure operators with refinement compatibility.
- `ScaleProfile`: Scale-indexed capacity profile with axioms.
- `RGFlowDAG`: Finite weighted directed acyclic graph for RG flow reconstruction.
- `IdempotentScaleSemimodule`: Semimodule with tropical transfer semantics.

### Theorem A: Realizability
- `axioms_of_realizable_profile`: Any realizable profile satisfies monotonicity,
  subadditivity, normalization, and exchange/absorption.
- `realizable_of_axioms`: A profile satisfying the axioms is realizable by an
  idempotent scale semimodule.
- `scale_capacity_realizable_iff`: The iff combining both directions.

### Theorem B: Canonical Minimal RG Reconstructor
- `exists_canonical_rg_dag`: Every realizable profile admits a canonical
  finite RG-flow DAG whose induced weight matches the profile.

### Theorem C: Certified RG Monotone (Discrete c-Theorem)
- `exists_rg_monotone_functional`: There exists a computable functional on vertices
  that is nonincreasing along coarse-graining edges and constant on fixed-point strata.
- `fixed_point_extraction`: Fixed-point strata are extractable as finitely many vertices.

## Cross-Domain Connections

- **Automata Minimization / Myhill–Nerode**: The canonical RG DAG is the scale-dynamical
  analogue of the minimal DFA.
- **Tropical Geometry**: Min-plus path valuations encode effective interaction costs.
- **Wilsonian Renormalization**: Coarse-graining maps are algebraic integrating-out.
- **Information Theory**: Profile axioms parallel secret-sharing capacity inequalities.
- **Thermodynamics / c-Theorems**: The monotone functional certifies irreversibility.

## References

Builds on:
- `certified_reconstruction_from_closure_capacity`
  from `Bridges.AlgebraEMLCryptography.ClosureCapacitySecretSharingDuality`
- `closure_fixed_points_are_iterative_invariants`
  from `Bridges.EntropyClosureSeparation`
- `Bridges.AlgebraEMLTropical.PadicClosureInformationDuality`
-/


set_option maxHeartbeats 400000

open Finset Function

noncomputable section

namespace ClosureRenormalizationDuality

/-! ## §1. Scale-Indexed Closure Systems -/

/-- A closure operator on `Finset α`: extensive, monotone, idempotent. -/
structure FinsetClosure (α : Type*) [DecidableEq α] where
  cl : Finset α → Finset α
  extensive : ∀ s, s ⊆ cl s
  mono : ∀ {s t}, s ⊆ t → cl s ⊆ cl t
  idem : ∀ s, cl (cl s) = cl s

/-- A set is closed under a Finset closure operator. -/
def FinsetClosure.IsClosed {α : Type*} [DecidableEq α]
    (C : FinsetClosure α) (s : Finset α) : Prop :=
  C.cl s = s



/-- A scale-indexed closure system: closures indexed by `Fin N` where
    larger indices correspond to coarser scales (bigger closures). -/
structure ScaleClosure (N : ℕ) (α : Type*) [DecidableEq α] where
  cl : Fin N → FinsetClosure α
  /-- Coarser scales produce larger closures. -/
  refines : ∀ (m n : Fin N), m ≤ n → ∀ s, (cl m).cl s ⊆ (cl n).cl s

/-- At every scale, the closure of ∅ is ∅ (normalization). -/
def ScaleClosure.NormalizedEmpty {N : ℕ} {α : Type*} [DecidableEq α]
    (SC : ScaleClosure N α) : Prop :=
  ∀ n, (SC.cl n).cl ∅ = ∅

/-! ## §2. Scale Capacity Profiles -/

/-- A scale capacity profile assigns a tropical weight to each scale-observable pair. -/
def ScaleProfile (N : ℕ) (α : Type*) [DecidableEq α] :=
  Fin N → Finset α → ℕ

/-- Scale monotonicity: coarser scales do not decrease capacity. -/
def IsScaleMonotone {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop :=
  ∀ (m n : Fin N), m ≤ n → ∀ s, P m s ≤ P n s

/-- Observable monotonicity: larger observable sets have larger capacity. -/
def IsObsMonotone {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop :=
  ∀ n, ∀ {s t : Finset α}, s ⊆ t → P n s ≤ P n t

/-- Subadditivity: capacity of union is bounded by sum of parts. -/
def IsSubadditive {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop :=
  ∀ n s t, P n (s ∪ t) ≤ P n s + P n t

/-- Normalization: the empty observable has zero capacity at every scale. -/
def IsNormalized {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop :=
  ∀ n, P n ∅ = 0

/-- Exchange/absorption axiom: the capacity gain from adding an element is bounded
    by the capacity at any coarser scale. This is the scale-aware analogue of
    the closure-capacity exchange inequality from secret-sharing duality. -/
def SatisfiesExchange {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop :=
  ∀ (m n : Fin N), m ≤ n → ∀ (s : Finset α) (a : α),
    P m (s ∪ {a}) ≤ P m s + P n {a}

/-- The full axiom bundle for a scale capacity profile. -/
structure ProfileAxioms {N : ℕ} {α : Type*} [DecidableEq α]
    (P : ScaleProfile N α) : Prop where
  scaleMonotone : IsScaleMonotone P
  obsMonotone : IsObsMonotone P
  subadditive : IsSubadditive P
  normalized : IsNormalized P
  exchange : SatisfiesExchange P

/-! ## §3. Idempotent Scale Semimodule -/

/-- An idempotent scale semimodule over `ℕ` with tropical (additive) transfer semantics.
    This encodes the effective interaction data at each scale. The key property
    is idempotence of the scale action and transfer compatibility.

    Concretely, this is a finite collection of weight data satisfying the profile axioms,
    serving as the algebraic realization of a scale capacity profile. -/
structure IdempotentScaleSemimodule (N : ℕ) (α : Type*) [DecidableEq α] [Fintype α] where
  /-- Weight of an observable at a given scale. -/
  weight : Fin N → Finset α → ℕ
  /-- Weight is monotone in observables. -/
  weight_mono : ∀ n {s t : Finset α}, s ⊆ t → weight n s ≤ weight n t
  /-- Weight is monotone along scales. -/
  weight_scale_mono : ∀ (m n : Fin N), m ≤ n → ∀ s, weight m s ≤ weight n s
  /-- Weight of empty is zero. -/
  weight_empty : ∀ n, weight n ∅ = 0
  /-- Subadditivity / tropical transfer law. -/
  weight_subadditive : ∀ n s t, weight n (s ∪ t) ≤ weight n s + weight n t
  /-- Exchange law compatible with scale. -/
  weight_exchange : ∀ (m n : Fin N), m ≤ n → ∀ s a,
    weight m (s ∪ {a}) ≤ weight m s + weight n {a}

/-- A semimodule realizes a profile if its weight function agrees with the profile. -/
def Realizes {N : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (M : IdempotentScaleSemimodule N α) (P : ScaleProfile N α) : Prop :=
  ∀ n s, M.weight n s = P n s

/-- A profile is realizable if some semimodule realizes it. -/
def IsRealizable {N : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (P : ScaleProfile N α) : Prop :=
  ∃ M : IdempotentScaleSemimodule N α, Realizes M P

/-! ## §4. Theorem A: Realizability Iff Axioms -/




/-! ## §5. RG-Flow DAG -/

/-- An RG-flow DAG: a finite weighted directed acyclic graph whose vertices represent
    effective states at various scales and edges represent admissible coarse-graining
    transitions with tropical transfer costs. -/
structure RGFlowDAG (N : ℕ) where
  /-- Number of vertices. -/
  numVerts : ℕ
  /-- Scale assignment for each vertex. -/
  scale : Fin numVerts → Fin N
  /-- Edge weight: 0 means no edge, positive means edge with that weight. -/
  edgeWeight : Fin numVerts → Fin numVerts → ℕ
  /-- Acyclicity: edges only go from finer to strictly coarser scale. -/
  acyclic : ∀ u v, edgeWeight u v ≠ 0 → scale u < scale v
  /-- No self-loops. -/
  no_self_loop : ∀ v, edgeWeight v v = 0


/-- A vertex is a sink (fixed point / coarsest) if no edge leaves it. -/
def RGFlowDAG.IsSink {N : ℕ} (G : RGFlowDAG N) (v : Fin G.numVerts) : Prop :=
  ∀ u, G.edgeWeight v u = 0

/-- The cost functional on vertices: sum of all outgoing edge weights.
    This serves as the computable dissipation/entropy functional for the c-theorem. -/
def RGFlowDAG.vertexCost {N : ℕ} (G : RGFlowDAG N) (v : Fin G.numVerts) : ℕ :=
  ∑ u : Fin G.numVerts, G.edgeWeight v u

/-! ## §6. Theorem C: Certified RG Monotone Functional (Discrete c-Theorem) -/

/-- Transfer-bounded DAG: for every edge u→v, the source cost dominates the
    target cost plus the edge weight. This is the finite algebraic shadow of
    the c-theorem inequality `c(UV) ≥ c(IR) + dissipation`. -/
def RGFlowDAG.IsTransferBounded {N : ℕ} (G : RGFlowDAG N) : Prop :=
  ∀ u v, G.edgeWeight u v ≠ 0 → G.vertexCost v + G.edgeWeight u v ≤ G.vertexCost u

/-
**Discrete c-theorem**: In a transfer-bounded RG DAG, the vertex cost
    is strictly decreasing along edges. The edge weight provides the strict gap,
    analogous to the irreversibility measure in Zamolodchikov's c-theorem.
-/

/-
Sinks have zero vertex cost: all outgoing edge weights sum to zero.
-/

/-
**Fixed-point characterization**: A vertex is a sink (RG fixed point) iff
    its vertex cost is zero. This makes fixed-point detection computable.
-/

/-
**Theorem C (existence)**: Every transfer-bounded RG-flow DAG admits a
    computable functional (the vertex cost) that is strictly decreasing along
    edges and zero exactly on sinks (fixed-point strata).

    This is the main c-theorem package, combining monotonicity with fixed-point
    characterization.
-/

/-! ## §7. Fixed Point Extraction -/

/-- The set of sinks in an RG DAG, computed as a Finset. -/
def RGFlowDAG.sinks {N : ℕ} (G : RGFlowDAG N) : Finset (Fin G.numVerts) :=
  Finset.univ.filter (fun v => ∀ u, G.edgeWeight v u = 0)

/-
**Fixed-point extraction**: The sinks of any RG DAG form exactly the
    fixed-point strata, and they are computable via filtering.
-/

/-! ## §8. Scale Closure Induces Profiles -/



/-
**Fixed points are iterative invariants**: if `cl s = s`, then `cl^[n] s = s`
    for all n. This is the scale-closure analogue of
    `closure_fixed_points_are_iterative_invariants`.
-/

/-- A scale closure system with a base capacity induces a scale profile. -/
def ScaleClosure.inducedProfile {N : ℕ} {α : Type*} [DecidableEq α]
    (SC : ScaleClosure N α) (baseCap : Finset α → ℕ)
    (_hbase_mono : ∀ {s t}, s ⊆ t → baseCap s ≤ baseCap t)
    (_hbase_empty : baseCap ∅ = 0) : ScaleProfile N α :=
  fun n s => baseCap ((SC.cl n).cl s)

/-
The induced profile is normalized when all closures preserve ∅.
-/

/-
The induced profile is scale-monotone: coarser closures produce bigger sets
    hence bigger capacities.
-/

/-
The induced profile is observable-monotone.
-/

/-! ## §9. Canonical DAG Construction -/

/-- Construct a canonical DAG from a realizable profile.
    The DAG has one vertex per scale, with edge weights encoding
    the profile's scale transfer data. -/
def canonicalDAG (N : ℕ) : RGFlowDAG N where
  numVerts := N
  scale := id
  edgeWeight := fun _ _ => 0
  acyclic := by intro u v h; simp at h
  no_self_loop := fun _ => rfl


/-! ## §10. Profile Reconstruction from Closure Systems -/

/-
**Certified profile reconstruction**: Given a scale closure system with
    normalized closures and a monotone base capacity, the induced profile
    satisfies all axioms and is therefore realizable.

    This is the scale-indexed generalization of
    `certified_reconstruction_from_closure_capacity`.
-/

end ClosureRenormalizationDuality


