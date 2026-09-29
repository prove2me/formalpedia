-- Prove2me | Theorems.Thm_mme_dwz_labelled_automorphism_maps_useful_block_tensor
-- name    : mme_dwz_labelled_automorphism_maps_useful_block_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:15:25.250705+00:00
-- url     : https://prove2.me/theorems/5ee49512-dfa7-409c-989e-54651310b7f6
-- title:
--   A label-aligned tensor automorphism transports each useful-block contribution
-- statement:
--   Let $D$ be a trilinear tensor whose $Z$-mode has a distinguished basis carrying useful-block labels. Suppose modewise linear automorphisms $F_0,F_1,F_2$ fix $D$, and $F_2$ permutes the distinguished basis in such a way that every label $b$ is moved by one fixed permutation $\sigma$. If $D_b$ denotes the singleton contribution of label $b$, then
--
--   $$
--   (F_0\otimes F_1\otimes F_2)(D_b)=D_{\sigma(b)}.
--   $$
--
--   Thus a common automorphism aligned on Z-basis labels transports every useful-block tensor by exactly the same public label permutation. This is the local interface needed to turn the DWZ grouped position shuffle into the shuffled nonhole-block sum of Claim 5.9.
--
--   **Formalization Note** The statement uses the opaque labelled standard-data bundle, preventing downstream specializations from unfolding the fifteen-factor Kronecker basis.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, the common variable relabeling which sends each available block to the corresponding shuffled block, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Mathlib.Tactic.FinCases

open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_labelled_automorphism_maps_useful_block_tensor
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m)
    (move : Equiv.Perm (DWZStandardBlock m))
    (F : ∀ i : Fin 3, D.X.V i ≃ₗ[K] D.X.V i)
    (hFtensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) D.X.t = D.X.t)
    (hFbasis : ∀ W : GroupedAllowedWords.{u} m,
      ∃ W' : GroupedAllowedWords.{u} m,
        F 2 (D.basis W) = D.basis W' ∧
          D.label W' = move (D.label W))
    (block : DWZStandardBlock m) :
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (dwzLabelledUsefulBlockTensor K m D block) =
      dwzLabelledUsefulBlockTensor K m D (move block) := by
  sorry
