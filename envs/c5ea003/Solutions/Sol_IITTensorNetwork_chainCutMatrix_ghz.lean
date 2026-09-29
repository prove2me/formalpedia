-- Prove2me | solution 1 for IITTensorNetwork.chainCutMatrix_ghz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:40:37.201013+00:00
-- url     : https://prove2.me/submissions/49563f70-0743-48eb-8d95-961e7df57ede

-- Sol generated from Novelty/IITTensorNetworkPhi.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IntegratedInformation
import Theorems.Thm_IITTensorNetwork_constCfg_injective
import Theorems.Thm_IITTensorNetwork_glue_const_iff

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
theorem solution{l : ℕ} (hl : l ≤ n) (hl1 : 1 ≤ l) :
    chainCutMatrix (ghzState n d) l hl
      = maxEnt (constCfg l d) (constCfg (n - l) d) := by
  ext f g
  have hcard : (Fintype.card (Fin d) : ℝ) = (d : ℝ) := by simp
  have hRHS : maxEnt (constCfg l d) (constCfg (n - l) d) f g
      = (((Real.sqrt d)⁻¹ : ℝ) : ℂ)
        * ∑ x : Fin d, (if constCfg l d x = f then (1 : ℂ) else 0)
            * (if constCfg (n - l) d x = g then (1 : ℂ) else 0) := by
    simp only [maxEnt, maxEntState, Matrix.smul_apply, Matrix.mul_apply, isoMatrix,
      Matrix.conjTranspose_apply, RCLike.star_def, smul_eq_mul, hcard]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : constCfg (n - l) d x = g <;> simp [h]
  rw [hRHS]
  simp only [chainCutMatrix, Matrix.of_apply, ghzState]
  by_cases hconst : ∀ i j, glue l hl f g i = glue l hl f g j
  · obtain ⟨x0, hx0f, hx0g⟩ := (glue_const_iff hl hl1 f g).mp hconst
    rw [if_pos hconst, Finset.sum_eq_single x0]
    · simp [hx0f, hx0g]
    · intro x _ hx
      have : constCfg l d x ≠ f := by
        rw [hx0f]
        exact fun h => hx (constCfg_injective (by omega) h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ x0) h
  · rw [if_neg hconst]
    have hzero : ∀ x : Fin d, (if constCfg l d x = f then (1 : ℂ) else 0)
        * (if constCfg (n - l) d x = g then (1 : ℂ) else 0) = 0 := by
      intro x
      by_cases h1 : constCfg l d x = f
      · by_cases h2 : constCfg (n - l) d x = g
        · exact absurd ((glue_const_iff hl hl1 f g).mpr ⟨x, h1.symm, h2.symm⟩) hconst
        · simp [h2]
      · simp [h1]
    rw [Finset.sum_congr rfl (fun x _ => hzero x)]
    simp
