-- Prove2me | Definitions.Def_Bridges_GraphTheory_CayleyCharacterSpectra
-- name    : Bridges_GraphTheory_CayleyCharacterSpectra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:16.479647+00:00
-- url     : https://prove2.me/theorems/59affa23-560c-4808-a9f0-e3a0d0565400
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_CayleyCharacterSpectra
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.CayleyCharacterSpectra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/CayleyCharacterSpectra.lean by skeleton subtraction
import Mathlib
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic
/-
# A character-theoretic bridge for Cayley graph walk statistics

Finite abelian groups carry two very different kinds of "observables":

* **harmonic ones** — sums of additive characters `ψ : AddChar G ℂ` over a subset `S`;
* **graph-theoretic ones** — counts of closed walks in the Cayley graph `Cay(G,S)`.

This file proves that the two coincide, and that both are governed by a purely
enumerative group-theoretic quantity: the number of length-`k` *relations*
`s₁ + ⋯ + s_k = 0` with all `sᵢ ∈ S`.

The main results are

* `adjMatrix_mulVec_char` — each character is an eigenvector of the Cayley
  adjacency matrix, with eigenvalue the character sum `∑ s ∈ S, ψ s`;
* `trace_pow_eq_charEigen_sum` — the trace of the `k`-th power of the adjacency
  matrix is the `k`-th power sum of the character eigenvalues (proved by
  diagonalisation in the Pontryagin dual basis of `G → ℂ`);
* `charEigen_pow_sum_eq_card_mul_relationCount` — that power sum equals
  `|G| ⬝ #{(s₁,…,s_k) ∈ Sᵏ : ∑ sᵢ = 0}`;
* `closedWalk_count_eq_card_mul_relationCount` — hence the total number of
  closed `k`-walks in the Cayley graph equals `|G|` times the number of
  length-`k` relations in `S`.

This is an exact mechanism behind the cycle-count regularities recorded in the
Cayley graph census of *Learning the Graphical Nature of Symmetries*: cycle-type
statistics of a Cayley graph are not extra data, they are the additive
combinatorics of the connection set, read through Fourier analysis on the group.
-/


open Finset
open scoped Matrix

namespace CayleyCharacterSpectra

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The Cayley graph -/

/-- The Cayley graph of the finite abelian group `G` with respect to a symmetric
connection set `S` that does not contain `0`. -/
def cayleyGraph (S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S) :
    SimpleGraph G where
  Adj x y := y - x ∈ S
  symm := by
    intro x y h
    have := hsymm _ h
    simpa [neg_sub] using this
  loopless := ⟨fun x h => h0 (by simpa using h)⟩

instance instDecidableAdj (S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S) :
    DecidableRel (cayleyGraph S hsymm h0).Adj :=
  fun x y => decidable_of_iff (y - x ∈ S) Iff.rfl



/-! ## Character eigenvalues -/

/-- The character sum attached to a connection set: the eigenvalue of the Cayley
adjacency matrix on the eigenvector `ψ`. -/
def charEigen (S : Finset G) (psi : AddChar G ℂ) : ℂ := ∑ s ∈ S, psi s




/-! ## Diagonalisation in the Pontryagin dual basis -/






/-! ## The enumerative side -/

/-- The number of length-`k` relations in `S`: tuples `(s₁,…,s_k) ∈ Sᵏ` with
`s₁ + ⋯ + s_k = 0`. -/
def relationCount (S : Finset G) (k : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k => S).filter (fun p => ∑ i, p i = 0)).card



/-! ## The bridge -/



/-! ## Consequences and a worked example -/





end

end CayleyCharacterSpectra


