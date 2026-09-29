-- Prove2me | solution 1 for IITTensorNetwork.glue_const_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:38:56.513263+00:00
-- url     : https://prove2.me/submissions/48105ed4-2dfc-406c-9b49-a49714e3c74b

-- Sol generated from Novelty/IITTensorNetworkPhi.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IntegratedInformation

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
theorem solution{l : ℕ} (hl : l ≤ n) (hl1 : 1 ≤ l) (f : Fin l → Fin d)
    (g : Fin (n - l) → Fin d) :
    (∀ i j, glue l hl f g i = glue l hl f g j)
      ↔ ∃ x, f = constCfg l d x ∧ g = constCfg (n - l) d x := by
  constructor
  · intro h
    refine ⟨glue l hl f g ⟨0, by omega⟩, ?_, ?_⟩
    · funext i
      simp only [constCfg]
      have hfi : glue l hl f g ⟨(i : ℕ), by have := i.isLt; omega⟩ = f i := by
        simp [glue, i.isLt]
      rw [← hfi]
      exact h _ _
    · funext j
      simp only [constCfg]
      have hgj : glue l hl f g ⟨l + (j : ℕ), by have := j.isLt; omega⟩ = g j := by
        have hlt : ¬ (l + (j : ℕ) < l) := by omega
        simp only [glue, dif_neg hlt]
        congr 1
        apply Fin.ext
        simp
      rw [← hgj]
      exact h _ _
  · rintro ⟨x, rfl, rfl⟩
    have hval : ∀ i : Fin n, glue l hl (constCfg l d x) (constCfg (n - l) d x) i = x := by
      intro i
      by_cases h : (i : ℕ) < l <;> simp [glue, constCfg, h]
    intro i j
    rw [hval i, hval j]
