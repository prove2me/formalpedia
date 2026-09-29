-- Prove2me | Definitions.Def_Novelty_StoneDualNeuralNetwork
-- name    : Novelty_StoneDualNeuralNetwork
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:42:05.971302+00:00
-- url     : https://prove2.me/theorems/19ec9439-210a-4e06-82d7-bbad210f7309
-- title:
--   Aether Catalog definitions — Novelty_StoneDualNeuralNetwork
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StoneDualNeuralNetwork`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StoneDualNeuralNetwork.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_NeuralCoding

/-!
# Stone Duality for Neural Networks: Activation Patterns as a Boolean Algebra

A neural network with `k` threshold neurons assigns to every input `x` an
**activation pattern** — the tuple of on/off states of its neurons.  This file
develops the *Stone-dual* picture of such a network:

* The **pattern space** `P = Fin k → Bool` is the finite space of all activation
  patterns.  Given the discrete topology it is a **Stone space** (compact,
  Hausdorff, totally disconnected) and its Boolean algebra of clopen sets is the
  full powerset `Set P`.
* A network is an **activation map** `act : X → P` from the input space.  Its
  **Stone dual** is the *region map* `region act : Set P → Set X`,
  `S ↦ act ⁻¹' S`, sending a set of patterns to the region of inputs realizing
  one of them.
* The region map is a **homomorphism of Boolean algebras**: it commutes with
  `⊥, ⊤, ∪, ∩, ᶜ, \\` and is monotone.  It is **injective exactly when every
  pattern is realized** (`act` surjective) — the algebraic shadow of Stone
  duality's reconstruction theorem.
* The **atoms** of `Set P` are the singletons `{p}`, whose images are the
  **activation cells** `act ⁻¹' {p}`.  These cells are pairwise disjoint, cover
  the input space, and a cell is nonempty exactly when its pattern is realized.
* For a **linear-threshold (perceptron) network** each cell is an intersection of
  affine half-spaces, hence **convex**, tying the algebra and topology back to the
  geometry of the input space.

The pattern space reuses `NeuralCoding.NeuralCode` from the catalog, so the
capacity count `Fintype.card (NeuralCode k) = 2 ^ k` feeds directly into the
count of distinct network regions, `2 ^ (2 ^ k)`.

-- !-- Lab Notes -- !--

* **Hypothesis.**  Every neural network `f : ℝ^n → ℝ^m` (more precisely, every
  network whose neurons induce an activation map `act : X → P`) has a "Stone
  dual": a Boolean algebra together with a duality map into the algebra of input
  regions, mirroring the correspondence between a Boolean algebra and the clopen
  algebra of its Stone space of ultrafilters.

* **Experiment.**  We modelled the dual concretely as the preimage map
  `region act = act ⁻¹' (·)` on the powerset of the finite pattern space.  On a
  finite discrete space every ultrafilter is principal, so the Stone space *is*
  the pattern space and its clopen algebra *is* `Set P`.  We proved the
  homomorphism laws, the injective ⇔ surjective duality, the atom/cell
  correspondence, the region count `2 ^ (2 ^ k)`, and — for perceptron networks
  — convexity of cells.

* **Analysis.**  The duality is exact (an isomorphism onto its image) precisely
  when the network realizes all `2 ^ k` patterns; otherwise the dual detects the
  *missing* patterns as the kernel of the homomorphism.  Convexity of cells is a
  purely geometric fact that the Boolean/topological layer is blind to, showing
  the perceptron layer carries strictly more structure than its Stone dual.

* **Critique.**  The finite-dimensional discreteness is essential: on an infinite
  Boolean algebra the Stone space carries non-principal ultrafilters, so the
  naive powerset model would fail.  We therefore state the topological results for
  a genuine (finite, discrete) Stone space rather than asserting them in general.

* **Synthesis.**  A neural network's decision structure is completely captured by
  a Boolean-algebra homomorphism from the clopen algebra of its (finite Stone)
  pattern space; the geometry of the input space enters only through the shape
  (here: convexity) of the atoms' images.
-/

open Function Set
open NeuralCoding

namespace StoneDualNN

/-! ## The pattern space as a Stone space -/

/-- The **pattern space** of a `k`-neuron network: the space of all activation
patterns.  It reuses `NeuralCoding.NeuralCode k = Fin k → Bool`. -/
def PatternSpace (k : ℕ) : Type := NeuralCode k

instance (k : ℕ) : Fintype (PatternSpace k) := inferInstanceAs (Fintype (NeuralCode k))
instance (k : ℕ) : DecidableEq (PatternSpace k) := inferInstanceAs (DecidableEq (NeuralCode k))
instance (k : ℕ) : TopologicalSpace (PatternSpace k) := ⊥
instance (k : ℕ) : DiscreteTopology (PatternSpace k) := ⟨rfl⟩






/-! ## The Stone dual: the region homomorphism -/

variable {X : Type*} {k : ℕ}

/-- The **region map** (Stone dual) of an activation map `act`: it sends a set of
patterns `S` to the region of inputs whose pattern lies in `S`. -/
def region (act : X → PatternSpace k) (S : Set (PatternSpace k)) : Set X := act ⁻¹' S










/-! ## Atoms and activation cells -/

/-- The **activation cell** of a pattern `p`: the inputs whose pattern is exactly
`p`.  It is the Stone-dual image of the atom `{p}`. -/
def cell (act : X → PatternSpace k) (p : PatternSpace k) : Set X := act ⁻¹' {p}






/-! ## Counting regions -/


/-! ## Perceptron networks: geometry of the cells -/

/-- The **linear-threshold (perceptron) activation map**: neuron `j` fires on
input `x` when its affine pre-activation `∑ i, w j i * x i + b j` is positive. -/
noncomputable def affineAct (n : ℕ) (w : Fin k → Fin n → ℝ) (b : Fin k → ℝ) :
    (Fin n → ℝ) → PatternSpace k :=
  fun x j => decide (0 < (∑ i, w j i * x i) + b j)




end StoneDualNN


