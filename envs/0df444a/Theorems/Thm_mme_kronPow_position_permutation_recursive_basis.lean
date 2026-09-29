-- Prove2me | Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
-- name    : mme_kronPow_position_permutation_recursive_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:10:47.326101+00:00
-- url     : https://prove2.me/theorems/ffae7532-5638-4a22-a994-347ebc955a65
-- title:
--   Position permutations agree with recursive tensor-power word reindexing
-- statement:
--   Let $T$ be a three-mode tensor and let $b$ be a basis in one mode. The recursively parenthesized mode space of $T^{\otimes n}$ has a recursive word basis indexed by `PowIndex`. For every permutation $e$ of the $n$ positions, the explicit ambient position automorphism sends the recursive basis vector labelled by $w$ to the vector labelled by the recursively reindexed word:
--
--   $$
--   P_e(B_w)=B_{e\cdot w}.
--   $$
--
--   Here the letter in new position $r$ is the letter formerly read at position $e(r)$. This identifies the ordinary function-word convention used by the ambient tensor automorphism with the recursive word convention used by the DWZ available-component projection, including the zero-power case.
--
--   **Formalization Note** `PowIndex.reindex e w` is characterized by `PowIndex.get _ (PowIndex.reindex e w) r = PowIndex.get _ w (e r)`.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173. This is the exact word-index interface needed to apply the common position shuffle to the available Z-word subspace.

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronPow_position_permutation_recursive_basis
    {K : Type u} [Field K]
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ)
    (e : Equiv.Perm (Fin n)) (w : PowIndex ι n) :
    kronPowModePositionEquiv T i b n e
        (kronPowModeBasis T i b n w) =
      kronPowModeBasis T i b n (PowIndex.reindex e w) := by
  sorry
