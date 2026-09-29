-- Prove2me | Theorems.Thm_CayleyCharacterSpectra_adjMatrix_mulVec_char
-- name    : CayleyCharacterSpectra.adjMatrix_mulVec_char
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:52.771968+00:00
-- url     : https://prove2.me/theorems/838c57b9-a45b-4036-a1ac-2fce409f5a61
-- title:
--   Characters are eigenvectors of the Cayley adjacency matrix.
-- statement:
--   **Characters are eigenvectors of the Cayley adjacency matrix.**  This is the
--   first half of the bridge: a purely harmonic object (the character sum over `S`)
--   is an eigenvalue of a purely combinatorial object (the adjacency operator).
--
--   ```lean
--   theorem CayleyCharacterSpectra.adjMatrix_mulVec_char(S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S)
--       (psi : AddChar G ℂ) :
--       (cayleyGraph S hsymm h0).adjMatrix ℂ *ᵥ (fun x => psi x) =
--         charEigen S psi • (fun x => psi x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/CayleyCharacterSpectra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/CayleyCharacterSpectra.lean#L86

-- Thm stub generated from Bridges/GraphTheory/CayleyCharacterSpectra.lean
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





/-! ## Character eigenvalues -/

theorem CayleyCharacterSpectra.adjMatrix_mulVec_char(S : Finset G) (hsymm : ∀ s ∈ S, -s ∈ S) (h0 : (0 : G) ∉ S)
    (psi : AddChar G ℂ) :
    (cayleyGraph S hsymm h0).adjMatrix ℂ *ᵥ (fun x => psi x) =
      charEigen S psi • (fun x => psi x) := by sorry
