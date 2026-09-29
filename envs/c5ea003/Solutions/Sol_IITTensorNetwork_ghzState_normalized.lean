-- Prove2me | solution 1 for IITTensorNetwork.ghzState_normalized
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:40.060406+00:00
-- url     : https://prove2.me/submissions/6440a701-5120-4cc9-9d5d-cb8b2ab98b4c

-- Sol generated from Novelty/IITTensorNetworkPhi.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IntegratedInformation
import Theorems.Thm_IITTensorNetwork_constCfg_injective

/-! # Integrated information of a tensor network state

We attach to a quantum state of a chain of `n` sites with local dimension `d`
the integrated information `Φ` of Tononi's theory, formalized through the
catalog's `IntegratedInformation.CausalStructure`: the admissible cuts are the
`n - 1` bipartitions of the chain into a left block and a right block, and the
information destroyed by a cut is the quantum mutual information carried across
that cut by the state.  Thus, *by construction*,

`Φ = min over bipartitions of the quantum mutual information`,

and the substantive content is in the theorems relating `Φ` to the tensor
network data:

* `phi_le_mutualInformation`, `exists_minimal_cut` : `Φ` is the minimum of the
  mutual information over bipartitions;
* `phi_eq_zero_iff_exists_product_cut` : `Φ = 0` exactly when the state
  factorizes (Schmidt rank one) across some cut, i.e. exactly when the state is
  *reducible* in the sense of IIT;
* `phi_le_two_log_of_bondDim` : a cut of bond dimension `χ` caps `Φ` at
  `2 log χ` — an MPS with bond dimension `2` has `Φ ≤ 2 log 2 = log 4`;
* `phi_ghz`, `phi_ghz_saturates_bond_bound` : the GHZ chain state has
  `Φ = 2 log d` where `d` is both its bond dimension
  (`hasBondDim_chainCutMatrix_ghz`) and its Schmidt rank at every cut; for
  `d = 2` this gives `Φ = 2 log 2 = log 4`, twice the logarithm of the Schmidt
  rank `2` (`phi_ghz_qubits`).
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork


variable {n d : ℕ}












variable {psi : (Fin n → Fin d) → ℂ}











variable {n d : ℕ}
















open IITTensorNetwork in
theorem solution(hn : 1 ≤ n) (hd : 0 < d) :
    ∑ s, ‖ghzState n d s‖ ^ 2 = 1 := by
  have hcount : (Finset.univ.filter (fun s : Fin n → Fin d => ∀ i j, s i = s j)).card = d := by
    have himage : (Finset.univ.filter (fun s : Fin n → Fin d => ∀ i j, s i = s j))
        = Finset.image (constCfg n d) Finset.univ := by
      ext s
      constructor
      · intro hs
        have h : ∀ i j, s i = s j := (Finset.mem_filter.mp hs).2
        refine Finset.mem_image.mpr ⟨s ⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
        funext i
        exact (h _ _).symm
      · intro hs
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i j => rfl⟩
    rw [himage, Finset.card_image_of_injective _ (constCfg_injective (k := n) (by omega)),
      Finset.card_univ, Fintype.card_fin]
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hval : ∀ s : Fin n → Fin d, ‖ghzState n d s‖ ^ 2
      = if (∀ i j, s i = s j) then ((d : ℝ))⁻¹ else 0 := by
    intro s
    by_cases h : ∀ i j, s i = s j
    · rw [if_pos h]
      simp only [ghzState, if_pos h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt d)⁻¹)]
      rw [sq, ← mul_inv, Real.mul_self_sqrt hd'.le]
    · simp [ghzState, h]
  rw [Finset.sum_congr rfl (fun s _ => hval s), ← Finset.sum_filter, Finset.sum_const, hcount,
    nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hd')]
