-- Prove2me | Definitions.Def_Bridges_UltrametricBarronCompressionDuality
-- name    : Bridges_UltrametricBarronCompressionDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:20.056603+00:00
-- url     : https://prove2.me/theorems/b8965de2-189a-4bb2-b77b-78cf8e55cf19
-- title:
--   Aether Catalog definitions — Bridges_UltrametricBarronCompressionDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricBarronCompressionDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricBarronCompressionDuality.lean by skeleton subtraction
import Mathlib
/-
# Ultrametric Barron Compression Duality via Prime-Congruence Approximation
# Semimodules and Certified Sparse Hierarchical Reconstruction

This file formalizes a **finite duality** between ultrametric proof-observer systems
and sparse hierarchical codes, with a certified reconstruction algorithm and
optimality theorem.

## Core Idea

Ultrametric spaces canonically produce trees (dendrograms): every ultrametric ball
is either disjoint from or contained in any other ball. A contraction operator on
such a space maps points to coarser levels of this tree. This gives a natural
**compression principle**: observer systems with ultrametric separation and
contraction stability are equivalent to sparse hierarchical codes, with complexity
controlled by an ultrametric Barron-type envelope.

## Main Results

### Structures
* `ApproxObserverSystem` — finite observer system with ultrametric distance,
  contraction operator, and proof-separation score
* `HierarchicalSparseCode` — hierarchical representation with tree parent structure,
  depth, and effective generator count
* `UltrametricSeparated` — ultrametric strong triangle inequality
* `ContractionStable` — contraction is distance-nonincreasing
* `DiagonalStable` — contraction is idempotent
* `ObserverEquivalent` — two systems induce the same reconstruction
* `PruningMinimal` — no smaller equivalent code exists

### Theorems
* `ultrametric_cluster_laminar` — ultrametric balls are laminar
* `contraction_nonexpansive` — contraction preserves distance ordering
* `contraction_idempotent_stabilizes` — idempotent contraction reaches fixed points
* `exists_hierarchical_sparse_code_of_barron_bound` — Barron → hierarchy direction
* `exists_observer_bound_of_hierarchical_code` — hierarchy → semimodule direction
* `observer_matrix_factors_through_tree` — factorization through tree
* `greedy_contraction_pruning_optimal` — greedy pruning is optimal
* `ultrametric_barron_compression_duality` — the main duality theorem
* `barron_complexity_eq_min_generators_nat` — Barron = minimal generators

## Bridges
* **Ultrametric geometry ↔ sparse approximation**: proof separation → compression norm
* **Tropical algebra ↔ hierarchical coding**: max-plus structure → tree factorization
* **Barron norms ↔ proof complexity**: variation norm → generator count
* **Contraction operators ↔ certified pruning**: nonexpansive maps → compression certificates

## Keywords
ultrametric approximation theory, Barron complexity, sparse hierarchical reconstruction,
certified pruning, proof-guided compression, prime congruence semimodules,
tropical sparse coding, observer duality, tree factorization, interpretable model
compression, multiresolution proof learning, residuation matrix factorization
-/


open Finset Function Set

noncomputable section

/-! ## §1. Core Observer System Structure -/

/-- An `ApproxObserverSystem` models a finite proof-observer system with:
- a finite carrier type `α` of proof states
- a coefficient type `R` (typically a semiring)
- an ultrametric distance `d` on states
- a contraction operator `C` for coarse-graining
- a proof-separation score measuring distinguishability
- a support weight functional for sparse approximation

This is the fundamental object bridging ultrametric geometry to
sparse hierarchical compression. -/
structure ApproxObserverSystem (α : Type*) (R : Type*) where
  /-- Ultrametric distance on proof states -/
  d : α → α → ℝ
  /-- Contraction / coarse-graining operator -/
  C : α → α
  /-- Proof separation score: how well can proofs be distinguished -/
  proofSep : α → α → ℝ
  /-- Weight function on finite subsets (support weight) -/
  supportWeight : Finset α → ℝ
  /-- Observer evaluation: maps states to coefficient values -/
  observe : α → α → R
  /-- Distance is nonnegative -/
  d_nonneg : ∀ x y, 0 ≤ d x y
  /-- Distance is zero iff equal -/
  d_eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y
  /-- Distance is symmetric -/
  d_symm : ∀ x y, d x y = d y x
  /-- Proof separation is nonneg -/
  proofSep_nonneg : ∀ x y, 0 ≤ proofSep x y
  /-- Support weight is nonneg -/
  supportWeight_nonneg : ∀ s, 0 ≤ supportWeight s

/-! ## §2. Predicates on Observer Systems -/

/-- `UltrametricSeparated S` asserts that the distance `d` on `S` satisfies the
strong (ultrametric) triangle inequality: d(x,z) ≤ max(d(x,y), d(y,z)),
and that proof separation controls reconstruction ambiguity. -/
structure UltrametricSeparated {α R : Type*} (S : ApproxObserverSystem α R) : Prop where
  /-- Strong triangle inequality -/
  ultra : ∀ a b c, S.d a c ≤ max (S.d a b) (S.d b c)
  /-- Proof separation is controlled by distance -/
  sep_le_d : ∀ a b, S.proofSep a b ≤ S.d a b

/-- `ContractionStable S` means the contraction operator `C` is
distance-nonincreasing: applying `C` never increases pairwise distances. -/
structure ContractionStable {α R : Type*} (S : ApproxObserverSystem α R) : Prop where
  /-- Contraction is nonexpansive -/
  contr : ∀ a b, S.d (S.C a) (S.C b) ≤ S.d a b

/-- `DiagonalStable S` means the contraction operator is idempotent:
C(C(a)) = C(a) for all a. This ensures contraction reaches fixed points. -/
structure DiagonalStable {α R : Type*} (S : ApproxObserverSystem α R) : Prop where
  /-- Contraction is idempotent -/
  idem : ∀ a, S.C (S.C a) = S.C a

/-- A prime-like congruence relation: two states are congruent if the contraction
maps them to the same image. This captures the "prime irreducibility" of
observer channels: states are indistinguishable iff they compress identically. -/
def primeCongruence {α R : Type*} (S : ApproxObserverSystem α R) (x y : α) : Prop :=
  S.C x = S.C y


/-! ## §3. Hierarchical Sparse Code -/

/-- A `HierarchicalSparseCode` represents a finite rooted tree encoding of
proof states. Each node has a parent (root is its own parent), a depth level,
and a label. The code captures hierarchical reconstruction via tree structure.

This is the "sparse coding" side of the compression duality: a hierarchical
representation where complexity is measured by effective generator count. -/
structure HierarchicalSparseCode (α : Type*) (R : Type*) where
  /-- Number of nodes in the tree -/
  numNodes : ℕ
  /-- Depth of the tree -/
  depth : ℕ
  /-- Number of effective generators (leaves / essential nodes) -/
  effectiveGenerators : ℕ
  /-- Effective generators bounded by number of nodes -/
  eff_le_nodes : effectiveGenerators ≤ numNodes
  /-- Reconstruction map: given a point, produce the approximation -/
  reconstruct : α → R

/-! ## §4. Observer Equivalence and Reconstruction Error -/

/-- Two systems are `ObserverEquivalent` if they induce the same
reconstruction on all states. -/
def ObserverEquivalent {α R : Type*}
    (S : ApproxObserverSystem α R) (T : HierarchicalSparseCode α R) : Prop :=
  ∀ x : α, S.observe x x = T.reconstruct x

/-- The reconstruction error between an observer system and a hierarchical code,
measured as the supremum of pointwise differences. -/
def ReconstructionError {α : Type*} [Fintype α] [Nonempty α]
    (S : ApproxObserverSystem α ℝ) (T : HierarchicalSparseCode α ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty fun x =>
    |S.observe x x - T.reconstruct x|

/-- The separation control of an observer system: the maximum proof separation
across all pairs. This controls how much reconstruction can deviate. -/
def separationControl {α : Type*} [Fintype α] [Nonempty α]
    {R : Type*} (S : ApproxObserverSystem α R) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty fun x =>
    Finset.sup' Finset.univ Finset.univ_nonempty fun y =>
      S.proofSep x y

/-- `PruningMinimal S T` means no hierarchical code with strictly fewer
effective generators is observer-equivalent to S. -/
def PruningMinimal {α R : Type*}
    (S : ApproxObserverSystem α R) (T : HierarchicalSparseCode α R) : Prop :=
  ObserverEquivalent S T ∧
  ∀ T' : HierarchicalSparseCode α R,
    ObserverEquivalent S T' → T.effectiveGenerators ≤ T'.effectiveGenerators


/-! ## §5. Barron Complexity -/

/-- The Barron complexity of an observer system: the minimum number of
effective generators across all observer-equivalent hierarchical codes.

In the finite setting, this is a natural number (or ⊤ if no equivalent
code exists, though for finite types one always exists). -/
def barronComplexity {α R : Type*}
    (S : ApproxObserverSystem α R) : ℕ :=
  sInf {n : ℕ | ∃ T : HierarchicalSparseCode α R,
    ObserverEquivalent S T ∧ T.effectiveGenerators = n}

/-! ## §6. Greedy Contraction Pruning Algorithm -/

/-- The canonical hierarchical code from an observer system: use the
contraction operator to build a single-level tree where each node
maps to its contraction image.

This is the simplest possible hierarchical encoding: depth 1,
with generators being the distinct images of C. -/
def canonicalHierarchicalCode {α : Type*} [Fintype α] [DecidableEq α]
    (R : Type*) (S : ApproxObserverSystem α R) : HierarchicalSparseCode α R where
  numNodes := Fintype.card α
  depth := 1
  effectiveGenerators := (Finset.univ.image S.C).card
  eff_le_nodes := le_trans Finset.card_image_le (by simp)
  reconstruct := fun x => S.observe (S.C x) (S.C x)

/-- The greedy contraction pruning: produces the canonical hierarchical code. -/
def greedyContractionPrune {α : Type*} [Fintype α] [DecidableEq α]
    (R : Type*) (S : ApproxObserverSystem α R) : HierarchicalSparseCode α R :=
  canonicalHierarchicalCode R S

/-! ## §7. Foundational Lemmas -/














/-! ## §8. Canonical Code Properties -/




/-! ## §9. Existence of Hierarchical Codes -/


/-
**Barron-to-hierarchy direction**: If the Barron complexity is at most K,
there exists a hierarchical sparse code with at most K effective generators
that is observer-equivalent.

This is the forward direction of the compression duality: low Barron complexity
implies existence of an efficient sparse hierarchical representation.
-/

/-
**Hierarchy-to-semimodule direction**: Every hierarchical code induces
a Barron complexity bound equal to its generator count.

This is the reverse direction: a sparse hierarchical code always produces
a proof-observer system of controlled complexity.
-/

/-
**Factorization through tree**: Under contraction-invariant observation,
observer systems factor through a tree code with generators equal to
the contraction image size.

This is the structural heart of the duality: the contraction operator forces
the observer system to have a tree-shaped factorization.
-/

/-! ## §10. Greedy Pruning Optimality -/

/-
The greedy contraction pruning produces an observer-equivalent code
when observation is contraction-invariant.
-/

/-
**Greedy contraction pruning optimality**: The greedy pruning produces
a code that is observer-equivalent, pruning-minimal, and has the minimum
number of effective generators among all equivalent codes.

This is the algorithmic optimality theorem: the simple greedy strategy
of merging contraction-equivalent states is optimal.
-/

/-! ## §11. Barron Complexity Characterization -/

/-
The Barron complexity set is nonempty: every finite observer system
has at least one equivalent hierarchical code.
-/

/-
Barron complexity is bounded by the cardinality of the type.
-/

/-
**Barron complexity equals minimum generators (nat version)**:
There exists a hierarchical code achieving the Barron complexity,
and it is pruning-minimal.

This converts the analytic Barron complexity into a discrete certified
optimum: a concrete tree code achieving the minimum.
-/

/-! ## §12. The Main Duality Theorem -/

/-
**Ultrametric Barron Compression Duality**: For a finite observer system with
ultrametric separation and contraction stability where observation is
contraction-invariant, the Barron complexity equals the contraction image size,
and there exists a pruning-minimal hierarchical code achieving this bound.

This is the founding theorem of ultrametric approximation theory for
proof-guided learning: proof geometry itself induces a compression norm,
and the optimal compression is computed by a simple greedy contraction.
-/

/-! ## §13. Bridge to Spectral Reconstruction -/

/-
**Ultrametric refines spectral reconstruction**: Under ultrametric separation
and contraction, the finite spectral reconstruction of states can be refined
into a hierarchical tree code. This bridges from the existing
`finite_spectral_reconstruction_bridge` infrastructure to the new
compression duality.

The key insight: spectral separation (observables distinguish states)
combined with ultrametric geometry (distances satisfy strong triangle inequality)
forces the reconstruction to have tree structure, yielding sparse hierarchical
codes rather than general spectral representations.
-/

/-! ## §14. Reconstruction Error Bounds -/

/-
Reconstruction error is zero for observer-equivalent codes.
-/

/-
Separation control is nonneg.
-/

end


