-- Prove2me | solution 1 for IITTensorNetwork.normalized_maxEnt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:57:09.157656+00:00
-- url     : https://prove2.me/submissions/0c4b2bc2-f478-409f-bd7e-69f45c78f557

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_normalized_iff_trace_rhoLeft
import Theorems.Thm_IITTensorNetwork_rhoLeft_maxEntState

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

open IITTensorNetwork


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]





















variable {α : Type*} [Fintype α] [DecidableEq α]





variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {u : γ → α} {v : γ → β}









lemma trace_rhoLeft_maxEntState (hu : Function.Injective u) (hv : Function.Injective v) (c : ℝ) :
    (rhoLeft (maxEntState c u v)).trace = ((Fintype.card γ : ℝ) * c ^ 2 : ℝ) := by
  rw [rhoLeft_maxEntState hu hv c, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_image_of_injective _ hu, Finset.card_univ, nsmul_eq_mul]




omit [DecidableEq γ] in
lemma maxEnt_sq (hγ : 0 < Fintype.card γ) :
    ((Real.sqrt (Fintype.card γ))⁻¹ : ℝ) ^ 2 = ((Fintype.card γ : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast hγ
  rw [sq, ← mul_inv, Real.mul_self_sqrt hpos.le]






open IITTensorNetwork in
theorem solution(hu : Function.Injective u) (hv : Function.Injective v)
    (hγ : 0 < Fintype.card γ) : Normalized (maxEnt u v) := by
  have hpos : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast hγ
  rw [normalized_iff_trace_rhoLeft, maxEnt, trace_rhoLeft_maxEntState hu hv, maxEnt_sq hγ]
  rw [mul_inv_cancel₀ (ne_of_gt hpos)]
  norm_num
