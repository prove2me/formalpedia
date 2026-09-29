-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
-- name    : Novelty_IITTensorNetworkWeightedGHZ
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:55:02.172986+00:00
-- url     : https://prove2.me/theorems/7eb3987d-dfb7-4f00-b794-8c0a9532d7a0
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkWeightedGHZ
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkWeightedGHZ`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkWeightedGHZ.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum

/-! # Schmidt form, weighted GHZ chains, and the exact value of `Φ`

This file completes the analysis of the mission conjecture "`Φ` is determined by
the Schmidt rank" by exhibiting, for every chain length `n ≥ 2` and every local
dimension `d`, a one-parameter family of matrix product states of *fixed* bond
dimension and *fixed* Schmidt rank `d` at every cut whose integrated information
sweeps out the whole interval `(0, 2 log d]`.

The tool is the *Schmidt form* of a bipartite pure state: a factorization

`M = L · diag(w) · Rᴴ`  with  `Lᴴ L = 1`,  `Rᴴ R = 1`,

i.e. an isometric change of basis on both sides bringing the state to diagonal
form with Schmidt coefficients `w`.  Main structural results:

* `vnEntropy_rhoLeft_of_schmidtForm`, `vnEntropy_rhoRight_of_schmidtForm`,
  `mutualInformation_of_schmidtForm` : the marginal entropies, and hence the
  mutual information across the cut, are the Shannon entropy of the squared
  Schmidt coefficients — *only the Schmidt spectrum matters*;
* `normalized_of_schmidtForm` : normalization is `∑ w² = 1`;
* `schmidtRank_of_schmidtForm` : the Schmidt rank is the number of Schmidt
  coefficients (when all are nonzero).

These are then applied to the **weighted GHZ chain state**
`ψ_w = ∑ₓ wₓ |x x ⋯ x⟩`, whose cut matrix is computed exactly
(`chainCutMatrix_weightedGhz`).  Consequences:

* `phi_weightedGhz` : `Φ(ψ_w) = 2 ∑ₓ -wₓ² log wₓ²` for every `n ≥ 2`;
* `schmidtRank_chainCutMatrix_weightedGhz` : the Schmidt rank at every cut is
  `d`, independently of `w`;
* `phi_unbalancedGhz_eq_two_mul_binEntropy` and
  `phi_unbalancedGhz_lt_two_log_two` : for `d = 2` the value is
  `2 H₂(c²)`, which is *strictly* below `2 log 2 = 2 log (Schmidt rank)`
  precisely when `c² ≠ 1/2`, while the state remains a bond-dimension-two MPS of
  Schmidt rank two at every bipartition.

Together with `phi_ghz` (the flat case) this settles the status of the
conjecture: `Φ` is bounded by, but not determined by, the Schmidt rank, and
equals `2 log (Schmidt rank)` exactly on flat spectra.
-/

open Finset Matrix Polynomial
open scoped ComplexOrder

namespace IITTensorNetwork

/-! ## States in Schmidt form -/

section SchmidtForm

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]







/-- The Schmidt-form matrix attached to Schmidt coefficients `w` and two
injective labellings of Schmidt vectors. -/
noncomputable def wMaxEnt (w : γ → ℝ) (u : γ → α) (v : γ → β) : Matrix α β ℂ :=
  isoMatrix u * Matrix.diagonal (fun x => (w x : ℂ)) * (isoMatrix v)ᴴ


end SchmidtForm

/-! ## The weighted GHZ chain state -/

section WeightedGHZ

variable {n d : ℕ} {w : Fin d → ℝ}

/-- The **weighted GHZ state** `∑ₓ wₓ |x x ⋯ x⟩` of a chain of `n` sites with
local dimension `d`.  The uniform weights `wₓ = d^{-1/2}` give the usual GHZ
state. -/
noncomputable def weightedGhzState (n d : ℕ) (w : Fin d → ℝ) : (Fin n → Fin d) → ℂ :=
  fun s => ∑ x, if s = constCfg n d x then (w x : ℂ) else 0











end WeightedGHZ

/-! ## The unbalanced GHZ family at `d = 2` -/

section UnbalancedGHZ

variable {n : ℕ}

/-- The weights of the unbalanced GHZ state `c|0⋯0⟩ + s|1⋯1⟩`. -/
def unbalancedWeights (c s : ℝ) : Fin 2 → ℝ := fun x => if x = 0 then c else s






end UnbalancedGHZ

end IITTensorNetwork


