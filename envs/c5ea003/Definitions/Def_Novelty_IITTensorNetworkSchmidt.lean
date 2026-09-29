-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkSchmidt
-- name    : Novelty_IITTensorNetworkSchmidt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:49:31.935979+00:00
-- url     : https://prove2.me/theorems/28ea8806-7929-4a86-bf67-2b0f6b8a1bdb
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkSchmidt
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkSchmidt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkSchmidt.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_IITTensorNetwork_vnEntropy_nonneg

/-! # Bipartite pure states, Schmidt rank and quantum mutual information

A pure state of a bipartite quantum system `A ⊗ B` with finite local index sets
`α` and `β` is encoded by its coefficient matrix `M : Matrix α β ℂ`, normalized
by `∑ i j, ‖M i j‖ ^ 2 = 1`.  The two reduced density matrices are `M * Mᴴ`
(on `A`) and `Mᴴ * M` (on `B`), the *Schmidt rank* across the cut is the rank of
`M`, and, since the global state is pure, the quantum mutual information across
the cut is

`I(A : B) = S(ρ_A) + S(ρ_B) - S(ρ_AB) = S(ρ_A) + S(ρ_B)`.

Main results:

* `rhoLeft_trace`, `rhoRight_trace` : the reduced matrices are density matrices;
* `schmidtRank_pos` : the Schmidt rank of a normalized state is at least one;
* `mutualInformation_nonneg`;
* `mutualInformation_le_two_log_schmidtRank` : the mutual information across a
  cut is at most `2 log (Schmidt rank)`;
* `mutualInformation_eq_zero_iff_schmidtRank_eq_one` : the mutual information
  vanishes exactly for product states across the cut;
* `vnEntropy_rhoLeft_eq_rhoRight` : the two marginal entropies of a pure state
  agree (equal-dimension parts), so `I(A : B) = 2 S(ρ_A)`;
* `mutualInformation_flat` : a flat Schmidt spectrum of rank `r` gives
  `I(A : B) = 2 log r`, the maximum allowed by the Schmidt rank.
-/

open Finset Matrix
open scoped ComplexOrder

namespace IITTensorNetwork

section Bipartite

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Normalization of the coefficient matrix of a pure bipartite state. -/
def Normalized (M : Matrix α β ℂ) : Prop := ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1

/-- The reduced density matrix on the left factor. -/
noncomputable def rhoLeft (M : Matrix α β ℂ) : Matrix α α ℂ := M * Mᴴ

/-- The reduced density matrix on the right factor. -/
noncomputable def rhoRight (M : Matrix α β ℂ) : Matrix β β ℂ := Mᴴ * M

/-- The Schmidt rank of a bipartite pure state across the given cut. -/
noncomputable def schmidtRank (M : Matrix α β ℂ) : ℕ := M.rank

omit [DecidableEq α] [DecidableEq β] in
lemma rhoLeft_posSemidef (M : Matrix α β ℂ) : (rhoLeft M).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose M

omit [DecidableEq α] [DecidableEq β] in
lemma rhoRight_posSemidef (M : Matrix α β ℂ) : (rhoRight M).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self M

omit [DecidableEq α] [DecidableEq β] in
lemma rhoLeft_trace {M : Matrix α β ℂ} (hM : Normalized M) : (rhoLeft M).trace = 1 := by
  have h : (rhoLeft M).trace = ∑ i, ∑ j, ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    simp [rhoLeft, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj']
  rw [h]
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hM

omit [DecidableEq α] [DecidableEq β] in
lemma rhoRight_trace {M : Matrix α β ℂ} (hM : Normalized M) : (rhoRight M).trace = 1 := by
  have h : (rhoRight M).trace = ∑ j, ∑ i, ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    simp [rhoRight, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_conj', mul_comm]
  rw [h, Finset.sum_comm]
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hM



/-- **Quantum mutual information** across the cut of a bipartite *pure* state:
the sum of the two marginal entropies (the global entropy vanishes). -/
noncomputable def mutualInformation (M : Matrix α β ℂ) : ℝ :=
  vnEntropy (rhoLeft M) + vnEntropy (rhoRight M)

/-- The entanglement entropy of the left marginal. -/
noncomputable def entanglementEntropy (M : Matrix α β ℂ) : ℝ := vnEntropy (rhoLeft M)



/-- Quantum mutual information across a cut is nonnegative. -/
theorem mutualInformation_nonneg {M : Matrix α β ℂ} (hM : Normalized M) :
    0 ≤ mutualInformation M :=
  add_nonneg (vnEntropy_nonneg (rhoLeft_posSemidef M) (rhoLeft_trace hM))
    (vnEntropy_nonneg (rhoRight_posSemidef M) (rhoRight_trace hM))




end Bipartite

section Symmetry

variable {α : Type*} [Fintype α] [DecidableEq α]



end Symmetry

section MaximallyEntangled

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {u : γ → α} {v : γ → β}



/-- The isometry matrix attached to a labelling `u : γ → α` of Schmidt vectors. -/
def isoMatrix (u : γ → α) : Matrix α γ ℂ := fun f x => if u x = f then 1 else 0



/-- The coefficient matrix of a maximally entangled state with Schmidt
coefficient `c` and Schmidt vectors labelled by `u` and `v`. -/
noncomputable def maxEntState (c : ℝ) (u : γ → α) (v : γ → β) : Matrix α β ℂ :=
  (c : ℂ) • (isoMatrix u * (isoMatrix v)ᴴ)






/-- The maximally entangled state of Schmidt rank `|γ|` attached to two
injective labellings of Schmidt vectors. -/
noncomputable def maxEnt (u : γ → α) (v : γ → β) : Matrix α β ℂ :=
  maxEntState ((Real.sqrt (Fintype.card γ))⁻¹) u v





end MaximallyEntangled

end IITTensorNetwork


