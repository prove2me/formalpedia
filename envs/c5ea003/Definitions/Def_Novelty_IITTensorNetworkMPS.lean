-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkMPS
-- name    : Novelty_IITTensorNetworkMPS
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:50:08.194848+00:00
-- url     : https://prove2.me/theorems/285fb431-1dd2-449e-8fb4-dbe2135fab28
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkMPS
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkMPS`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkMPS.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

/-! # Bond dimension of matrix product states and the Schmidt rank bound

A tensor network state has *bond dimension at most `χ`* across a cut when its
coefficient matrix factors through a `χ`-dimensional auxiliary (virtual) space.
This is exactly the structure of a matrix product state (MPS) cut open at one
bond.  We prove:

* `schmidtRank_le_of_hasBondDim` : bond dimension bounds the Schmidt rank;
* `mutualInformation_le_two_log_bondDim` : hence the quantum mutual information
  across the cut is at most `2 log χ`;
* `mpsCutMatrix_factorization` and `hasBondDim_mpsCutMatrix` : an explicit MPS
  built from local tensors of bond dimension `χ` has bond dimension `χ`;
* `mutualInformation_mps_bondDim_two_le` : for bond dimension `2`, the mutual
  information across the cut is at most `2 log 2 = log 4`, the value attained by
  a maximally entangled qubit pair.
-/

open Finset Matrix
open scoped ComplexOrder

namespace IITTensorNetwork

section BondDimension

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A bipartite coefficient matrix has *bond dimension at most `χ`* when it
factors through a `χ`-dimensional virtual space. -/
def HasBondDim (M : Matrix α β ℂ) (χ : ℕ) : Prop :=
  ∃ (L : Matrix α (Fin χ) ℂ) (R : Matrix (Fin χ) β ℂ), M = L * R






end BondDimension

section MPS

variable {l m d χ : ℕ}

/-- The ordered product of the local tensors of the left block along a
configuration of the left block. -/
noncomputable def leftProd (A : Fin l → Fin d → Matrix (Fin χ) (Fin χ) ℂ) (f : Fin l → Fin d) :
    Matrix (Fin χ) (Fin χ) ℂ :=
  Fin.foldr l (fun i acc => A i (f i) * acc) 1

/-- The ordered product of the local tensors of the right block along a
configuration of the right block. -/
noncomputable def rightProd (B : Fin m → Fin d → Matrix (Fin χ) (Fin χ) ℂ) (g : Fin m → Fin d) :
    Matrix (Fin χ) (Fin χ) ℂ :=
  Fin.foldr m (fun j acc => B j (g j) * acc) 1

/-- The coefficient matrix, across the bond joining the two blocks, of the
matrix product state with local tensors `A` (left block), `B` (right block) and
boundary vectors `vL`, `vR`. -/
noncomputable def mpsCutMatrix (A : Fin l → Fin d → Matrix (Fin χ) (Fin χ) ℂ)
    (B : Fin m → Fin d → Matrix (Fin χ) (Fin χ) ℂ) (vL vR : Fin χ → ℂ) :
    Matrix (Fin l → Fin d) (Fin m → Fin d) ℂ :=
  Matrix.of fun f g => vL ⬝ᵥ ((leftProd A f * rightProd B g) *ᵥ vR)

/-- The left environment matrix obtained by cutting the MPS at the bond. -/
noncomputable def mpsLeftEnv (A : Fin l → Fin d → Matrix (Fin χ) (Fin χ) ℂ) (vL : Fin χ → ℂ) :
    Matrix (Fin l → Fin d) (Fin χ) ℂ :=
  Matrix.of fun f b => (vL ᵥ* leftProd A f) b

/-- The right environment matrix obtained by cutting the MPS at the bond. -/
noncomputable def mpsRightEnv (B : Fin m → Fin d → Matrix (Fin χ) (Fin χ) ℂ) (vR : Fin χ → ℂ) :
    Matrix (Fin χ) (Fin m → Fin d) ℂ :=
  Matrix.of fun b g => (rightProd B g *ᵥ vR) b






end MPS

end IITTensorNetwork


