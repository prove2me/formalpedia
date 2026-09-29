-- Prove2me | Theorems.Thm_mme_dwz_fine_z_unique_owner_direct_sum_restrict
-- name    : mme_dwz_fine_z_unique_owner_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:44:24.082876+00:00
-- url     : https://prove2.me/theorems/6b38e426-cef2-4bb5-a45d-2c3e25369020
-- title:
--   DWZ additional zeroing: unique fine-Z ownership gives a direct-sum restriction
-- statement:
--   Let $T$ be a trilinear tensor over a field, equipped with a finite refined grading, and let $a_j$ be the fully refined grading address of each retained outer copy $j$. In contrast to a coarse Table-2 address, the mode-two word $a_j^{(Z)}$ records the surviving fine $Z$-block data after the additional zeroing steps. Let $o$ be a partial owner map from fine $Z$-words to retained copies. Assume: (i) $o(a_j^{(Z)})=j$ for every retained address; (ii) every coordinatewise nonzero mixed address assembled from three retained addresses has equal $X$- and $Y$-owners; and (iii) the fine $Z$-word occurring in every such supported mixed address is owned by its $X$-owner. Then every supported mixed choice is diagonal, and hence
--
--   $$
--   ⊕_j B_G(a_j) ≼ T^{⊗ N}.
--   $$
--
--   This theorem is the tensor-algebra consequence of unique fine-$Z$ ownership. It makes no inducedness assumption on coarse $Z$-words, which may be shared by several retained triples in asymmetric hashing. The hypothesis corresponding to (iii), `hSupportedFineZOwner`, remains the hard source-specific obligation: it must be derived from Claim 6.2 and the construction of Additional Zeroing-Out Step 2. Thus the theorem does not itself construct the DWZ zeroing or identify the resulting address blocks with broken standard-form tensors.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1: Step 3 and Additional Zeroing-Out Step 1 (printed p. 51, PDF p. 52), Claim 6.2, Definition 6.3, and Additional Zeroing-Out Step 2 (printed p. 52, PDF p. 53), and the independent-triple/Hole-Lemma handoff in Step 4 (printed p. 53, PDF p. 54); the resulting value bound is Equation (25) on printed p. 58 (PDF p. 59). https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_induced_graded_address_blocks_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fine_z_unique_owner_direct_sum_restrict
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (fineZOwner : (Fin N → Fin t) → Option (Fin k))
    (hOwned : ∀ j : Fin k,
      fineZOwner (fineAddress j 2) = some j)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedFineZOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      fineZOwner (fineAddress (js 2) 2) = some (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  sorry
