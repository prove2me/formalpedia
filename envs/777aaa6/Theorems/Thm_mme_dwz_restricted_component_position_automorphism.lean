-- Prove2me | Theorems.Thm_mme_dwz_restricted_component_position_automorphism
-- name    : mme_dwz_restricted_component_position_automorphism
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:03:52.178127+00:00
-- url     : https://prove2.me/theorems/cc25257e-7cc1-4698-a4a1-ab3a793a56df
-- title:
--   Position shuffles are automorphisms of each restricted DWZ component power
-- statement:
--   Fix a field $K$, one of the fifteen Table-2 component types $s$, a scale $m$, and a permutation $e$ of the $c_s m$ positions in that component power. Let $R_{s,m}$ be the literal DWZ component tensor obtained by retaining all $X$- and $Y$-words and precisely the $Z$-words with the prescribed split histogram. Then the common position permutation is realized by a linear automorphism $\Psi_i$ of every mode of $R_{s,m}$, and the three automorphisms fix its tensor exactly: $$\left(\bigotimes_{i=0}^{2} \Psi_i\right)R_{s,m}=R_{s,m}.$$ Moreover, on the canonical available-word basis of the restricted $Z$-mode, $\Psi_2$ sends the word $w$ exactly to the reindexed word $w\circ e$. The result is the one-component linear realization of the useful-block shuffle in Claim 5.9. It uses the same label permutation in all modes, rather than merely asserting an abstract isomorphism of quotient spaces, and its basis-level conclusion is the interface needed to tensorize the shuffle across all fifteen components. It includes zero-size components.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the common within-component variable relabeling used in Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
import Theorems.Thm_mme_dwz_component_word_allowed_reindex_iff
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_dwz_restricted_component_position_automorphism
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm (Fin (MME.DWZTable2Counts.component s * m))) :
    ∃ Ψ : ∀ i : Fin 3,
        (restrictedComponentPower K s m).V i ≃ₗ[K]
          (restrictedComponentPower K s m).V i,
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (restrictedComponentPower K s m).t =
        (restrictedComponentPower K s m).t ∧
      ∀ w : AvailableComponentWord.{u} s m,
        Ψ 2 (restrictedComponentZBasis K s m w) =
          restrictedComponentZBasis K s m
            ⟨PowIndex.reindex e w.1,
              (mme_dwz_component_word_allowed_reindex_iff
                s m e w.1).2 w.2⟩ := by
  sorry
