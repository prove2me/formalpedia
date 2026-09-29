-- Prove2me | solution 1 for CayleyCharacterSpectra.adjMatrix_mulVec_char
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:05:58.085763+00:00
-- url     : https://prove2.me/submissions/69a36bd8-ac8c-41ef-b643-ffa9690ad88f

-- Sol generated from Bridges/GraphTheory/CayleyCharacterSpectra.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_CayleyCharacterSpectra
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

open CayleyCharacterSpectra

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The Cayley graph -/



omit [Fintype G] [DecidableEq G] in
@[simp] lemma cayleyGraph_adj (S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S)
    (x y : G) : (cayleyGraph S hsymm h0).Adj x y ↔ y - x ∈ S := Iff.rfl


/-! ## Character eigenvalues -/





/-! ## Diagonalisation in the Pontryagin dual basis -/






/-! ## The enumerative side -/




/-! ## The bridge -/



/-! ## Consequences and a worked example -/







open CayleyCharacterSpectra in
theorem solution(S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S)
    (psi : AddChar G ℂ) :
    (cayleyGraph S hsymm h0).adjMatrix ℂ *ᵥ (fun x => psi x) =
      charEigen S psi • (fun x => psi x) := by
  ext x
  simp [charEigen, Matrix.mulVec, dotProduct]
  have h : (∑ y, if y - x ∈ S then psi y else 0) = ∑ s ∈ S, psi (x + s) := by
    rw [← Finset.sum_filter]
    have heq : Finset.filter (fun a => a - x ∈ S) Finset.univ = Finset.image (fun s => x + s) S := by
      ext a
      simp [sub_eq_add_neg, add_comm]
    rw [heq, Finset.sum_image]
    intro a _ b _ hab
    exact add_left_cancel hab
  rw [h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [mul_comm]
  rw [add_comm]
  show (psi (s + x) : ℂ) = (psi x : ℂ) * (psi s : ℂ)
  rw [add_comm s x]
  exact AddChar.map_add_eq_mul psi x s
