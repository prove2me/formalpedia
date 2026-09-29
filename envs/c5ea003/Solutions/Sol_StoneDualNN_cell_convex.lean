-- Prove2me | solution 1 for StoneDualNN.cell_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:33.721959+00:00
-- url     : https://prove2.me/submissions/aeb12133-04d4-497c-b9af-1d38b85c8b27

-- Sol generated from Novelty/StoneDualNeuralNetwork.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCoding
import Definitions.Def_Novelty_StoneDualNeuralNetwork

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

open StoneDualNN

/-! ## The pattern space as a Stone space -/


instance (k : ℕ) : DiscreteTopology (PatternSpace k) := ⟨rfl⟩






/-! ## The Stone dual: the region homomorphism -/

variable {X : Type*} {k : ℕ}











/-! ## Atoms and activation cells -/







/-! ## Counting regions -/


/-! ## Perceptron networks: geometry of the cells -/


/-- The linear pre-activation of neuron `j` is a linear map of the input. -/
theorem isLinearMap_preact (n : ℕ) (v : Fin n → ℝ) :
    IsLinearMap ℝ (fun x : Fin n → ℝ => ∑ i, v i * x i) := by
  constructor
  · intro x y
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  · intro c x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext i; ring




open StoneDualNN in
theorem solution(n : ℕ) (w : Fin k → Fin n → ℝ) (b : Fin k → ℝ)
    (p : PatternSpace k) :
    Convex ℝ (cell (affineAct n w b) p) := by
  have hcell : cell (affineAct n w b) p
      = ⋂ j, {x : Fin n → ℝ | affineAct n w b x j = p j} := by
    ext x
    simp only [cell, mem_preimage, mem_singleton_iff, mem_iInter, mem_setOf_eq]
    constructor
    · intro h j; rw [h]
    · intro h; funext j; exact h j
  rw [hcell]
  apply convex_iInter
  intro j
  have hlin := isLinearMap_preact n (w j)
  cases hpj : p j
  · have heq : {x : Fin n → ℝ | affineAct n w b x j = false}
        = {x | (∑ i, w j i * x i) ≤ -(b j)} := by
      ext x
      simp only [affineAct, mem_setOf_eq, decide_eq_false_iff_not, not_lt]
      constructor <;> intro h <;> linarith
    rw [heq]; exact convex_halfSpace_le hlin (-(b j))
  · have heq : {x : Fin n → ℝ | affineAct n w b x j = true}
        = {x | -(b j) < ∑ i, w j i * x i} := by
      ext x
      simp only [affineAct, mem_setOf_eq, decide_eq_true_eq]
      constructor <;> intro h <;> linarith
    rw [heq]; exact convex_halfSpace_gt hlin (-(b j))
