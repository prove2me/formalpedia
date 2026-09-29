-- Prove2me | Definitions.Def_Bridges_PrimeCongruenceGeneralizationDuality
-- name    : Bridges_PrimeCongruenceGeneralizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:11.311992+00:00
-- url     : https://prove2.me/theorems/27d39ab7-a463-4095-8cbc-f86682f57f9b
-- title:
--   Aether Catalog definitions — Bridges_PrimeCongruenceGeneralizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PrimeCongruenceGeneralizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PrimeCongruenceGeneralizationDuality.lean by skeleton subtraction
import Mathlib

/-! # Spectral Learning Theory for Neural Operads:
    Prime Congruence Generalization Duality

This file formalizes the foundations of **spectral learning theory for neural operads**,
a framework where generalization in machine learning is controlled by the geometry of
prime-like observational congruences rather than by raw combinatorics of labelings.

## Main Results

### Core Duality (Galois Connection)
* `ObsSpec.le_jointKer_VSet` — R ≤ I(V(R)): closure from below
* `ObsSpec.subset_VSet_jointKer` — C ⊆ V(I(C)): closure from above
* `ObsSpec.VSet_antitone` — V is order-reversing
* `ObsSpec.VSet_jointKer_VSet` — V(I(V(R))) = V(R): first idempotence
* `ObsSpec.jointKer_VSet_jointKer` — I(V(I(C))) = I(C): second idempotence
* `ObsSpec.galois_iff` — Galois connection characterization

### Radical-Closed Anti-Isomorphism
* `ObsSpec.VSet_radical_isSpectralClosed` — V maps radical congruences to closed sets
* `ObsSpec.jointKer_closed_isRadical` — I maps closed sets to radical congruences
* `ObsSpec.radical_le_iff_VSet_subset` — order-reversing correspondence
* `ObsSpec.radicalize_isRadical` — radicalization is radical
* `ObsSpec.radicalize_idempotent` — radicalization is idempotent

### Separation and Compression
* `ObsSpec.separation_implies_eq_radical` — separation ⟹ equality is radical
* `ObsSpec.jointKer_univ_eq_of_sep` — separation ⟹ I(univ) = Eq

### Architecture Complexity
* `ObsSpec.spectralDim_le_architectureComplexity` — observer count ≤ complexity

## Bridge

Connects algebraic geometry (prime spectra, Galois connections, Nullstellensatz) →
machine learning (sample compression, shattering bounds) →
proof theory (observer semantics) →
operadic algebra (neural architecture composition).
-/

set_option maxHeartbeats 800000

open Classical

noncomputable section

open Finset Function

namespace ObsSpec

/-! ## Section 1: Core Definitions -/

/-- A neural architecture with depth, generator count, and width parameters. -/
structure NeuralArchitecture where
  depth : ℕ
  generatorCount : ℕ
  width : ℕ

/-- The complexity of a neural architecture. -/
def NeuralArchitecture.complexity (A : NeuralArchitecture) : ℕ :=
  A.depth * A.generatorCount * A.width

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Section 2: Observer Kernels and Vanishing Sets -/

/-- The joint kernel of a finset of observers: `x` and `y` are equivalent iff
    every observer in `C` maps them to the same value.

    Bridge: this is the intersection of observer kernels, the algebraic analog
    of intersecting prime ideals in commutative algebra. -/
def jointKer (obs : ι → S → ℕ) (C : Finset ι) (x y : S) : Prop :=
  ∀ i ∈ C, obs i x = obs i y

/-- The vanishing set of a relation `R`: observer indices whose kernel contains `R`.

    Bridge: the algebraic geometry analog of V(I) = {p ∈ Spec | I ⊆ p},
    transported from ideals to observational congruences. -/
def VSet (obs : ι → S → ℕ) (R : S → S → Prop) : Finset ι :=
  Finset.univ.filter (fun i => ∀ x y : S, R x y → obs i x = obs i y)

/-- A relation is **radical** if it equals the joint kernel of its vanishing set.

    Bridge: the analog of rad(I) = I in commutative algebra (the Nullstellensatz). -/
def ObsRadical (obs : ι → S → ℕ) (R : S → S → Prop) : Prop :=
  ∀ x y : S, R x y ↔ jointKer obs (VSet obs R) x y

/-- A finset is **spectrally closed** if it equals the vanishing set of its joint kernel.

    Bridge: these are the Zariski-closed subsets of the observer spectrum. -/
def SpectralClosed (obs : ι → S → ℕ) (C : Finset ι) : Prop :=
  C = VSet obs (jointKer obs C)

/-- The **separation axiom**: every distinct pair is distinguished by some observer.

    Bridge: the finite analog of the T₀ separation axiom for spectral spaces,
    or the Hausdorff condition for observer-based topologies. -/
def Separation (obs : ι → S → ℕ) : Prop :=
  ∀ x y : S, x ≠ y → ∃ i : ι, obs i x ≠ obs i y

/-- A finset of observers **separates** all distinct elements. -/
def IsSeparatingSet (obs : ι → S → ℕ) (C : Finset ι) : Prop :=
  ∀ x y : S, x ≠ y → ∃ i ∈ C, obs i x ≠ obs i y

/-- The radicalization of a relation: rad(R) = I(V(R)).

    Bridge: the closure operator that takes a congruence to its radical,
    analogous to the radical of an ideal in commutative algebra. -/
def radicalize (obs : ι → S → ℕ) (R : S → S → Prop) : S → S → Prop :=
  jointKer obs (VSet obs R)

/-! ## Section 3: Galois Connection

We prove that `V` (vanishing set) and `I` (joint kernel) form a **Galois connection**
between binary relations on `S` (ordered by pointwise implication) and finsets of
observers (ordered by reverse inclusion). This is the algebraic core of the duality. -/








/-! ## Section 4: Radical-Closed Anti-Isomorphism

The core duality: V and I restrict to mutually inverse, order-reversing bijections
between radical congruences and spectrally closed observer sets. This is the finite
algebraic analog of the Nullstellensatz / Stone duality. -/









/-! ## Section 5: Separation Theorem

The separation axiom — that distinct elements are distinguished by some observer —
is the finite analog of the T₀ condition in spectral topology. Under separation,
equality becomes a radical congruence, which is the finite Nullstellensatz. -/







/-! ## Section 6: Joint Kernel Lattice Properties -/




/-! ## Section 7: Compression Certificates -/

/-- A compression certificate for a labeled sample. -/
structure CompressionCert (obs : ι → S → ℕ) (D : Finset (S × Bool)) where
  support : Finset (S × Bool)
  support_sub : support ⊆ D
  witness : ι
  consistent : ∀ p ∈ support, (decide (obs witness p.1 = 0)) = p.2


/-! ## Section 8: Spectral Dimension and Architecture -/

end ObsSpec

namespace ObsSpec



variable {S : Type*} [Fintype S] [DecidableEq S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Section 9: Main Duality Theorem -/


/-! ## Section 10: Concrete Example

We demonstrate the duality on a concrete finite example: two observers on Fin 4
that separate all four elements. This shows the framework is computationally
instantiable, not just abstractly valid. -/

/-- Two observers on Fin 4 that separate all elements.
    Observer 0 splits {0,1} from {2,3}. Observer 1 splits {0,2} from {1,3}.
    Together they give a complete binary encoding. -/
def exObs : Fin 2 → Fin 4 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨0, _⟩, ⟨3, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨3, _⟩ => 1



end ObsSpec


