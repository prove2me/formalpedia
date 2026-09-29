-- Prove2me | Definitions.Def_Tropical_Round7DigitLattice
-- name    : Tropical_Round7DigitLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:25.483795+00:00
-- url     : https://prove2.me/theorems/31232325-8f0d-4f74-9644-3fae10d700b7
-- title:
--   Aether Catalog definitions — Tropical_Round7DigitLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Round7DigitLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Round7DigitLattice.lean by skeleton subtraction
import Mathlib

/-!
# Round-7 closure DIGITLATTICE: the digit-convolution relaxation is not isolated

Experiment 328 linearised the base-`b` digit equations of `N = p q` by setting
`w_{ij} = p_i q_j` and observed that the factorisation target sits *at* the
Gaussian heuristic, so lattice reduction returns generic short vectors instead
of the factorisation.  This file proves the exact structural reason, in the
smallest nontrivial case (two digits per factor), and it is a statement about
*all* `N`, not a heuristic:

* `digitVal_rankOne` : the encoding is faithful — the digit convolution of a
  rank-one matrix `w = u ⊗ v` evaluates to the product of the two numbers
  `u₀ + u₁ b` and `v₀ + v₁ b`.  Factorisations are exactly the rank-one
  solutions.
* `det_rankOne` : rank-one matrices have vanishing determinant; the determinant
  is therefore the obstruction that the linear relaxation throws away.
* `commutator_digitVal` : the "carry commutator" `w = [[0,1],[-1,0]]` lies in the
  kernel of the digit functional for *every* base `b`.  It has squared norm `2`,
  a constant independent of `N`.
* `exists_spurious_solution` : consequently every factorisation target has a
  **non-rank-one companion solution at squared distance at most `8`** — the
  relaxed problem has spurious solutions in an `O(1)` ball around the target,
  whatever the size of `N`.  Since the target's own squared norm grows like the
  product of the digit norms (`sqNorm_rankOne_ge_four` gives the first step),
  short-vector search cannot separate the factorisation from the noise.
-/

namespace Round7DigitLattice

open Finset

/-- The digit-convolution functional in base `b`: `w ↦ Σ_{i,j} w_{ij} b^{i+j}`,
for two-digit factors. -/
def digitVal (b : ℤ) (w : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  ∑ i : Fin 2, ∑ j : Fin 2, w i j * b ^ ((i : ℕ) + (j : ℕ))

/-- The rank-one (genuine factorisation) matrix `u ⊗ v`. -/
def rankOne (u v : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℤ := fun i j => u i * v j

/-- The two-digit number encoded by a digit vector. -/
def digitNum (b : ℤ) (u : Fin 2 → ℤ) : ℤ := u 0 + u 1 * b



/-- The carry commutator `[[0,1],[-1,0]]`. -/
def commMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]


/-- The squared Frobenius norm of a digit matrix. -/
def sqNorm (w : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := ∑ i : Fin 2, ∑ j : Fin 2, (w i j) ^ 2






end Round7DigitLattice


