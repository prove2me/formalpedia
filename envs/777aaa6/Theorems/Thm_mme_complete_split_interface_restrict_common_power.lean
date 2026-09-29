-- Prove2me | Theorems.Thm_mme_complete_split_interface_restrict_common_power
-- name    : mme_complete_split_interface_restrict_common_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:18:06.252099+00:00
-- url     : https://prove2.me/theorems/0c51dd82-9b14-495e-b964-517786c0372e
-- title:
--   A complete-profile interface restricts from its common ambient tensor power
-- statement:
--   Let T₁,…,Tᵣ be three-tensors over any field, each restricting from a common source S. Give every mode of every Tₜ a basis labelled by full level-ℓ words, and three complete-split profiles βₜ. For nonnegative ε and powers nₜ, let Rₜ be the simultaneous three-mode complete-profile restriction of Tₜ^{⊗nₜ}. Then ⊗ₜRₜ is an actual tensor restriction of S^{⊗(∑ₜnₜ)}. Empty products and zero powers are covered by the tensor-unit convention. This finite tensor-product statement neither asserts that the retained tensors are nonzero nor extracts a direct sum of independent copies. Canonical CW labels and asymptotic value lower bounds are separate obligations.
-- source:
--   Finite ambient-source realization of the interface tensor in Definition 4.1, printed p.15, using the restricted constituent powers in Definitions 3.4–3.6, printed p.14, of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2. https://arxiv.org/abs/2404.16349v2. Generalized to arbitrary basis-labelled constituents that individually restrict from a common source, and to every ε≥0; the finite restriction proof needs no upper bound on ε.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_CW_2376_address_block

open MME MME.CompleteSplit Module BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_interface_restrict_common_power
    {K : Type u} [Field K] {r ell : ℕ}
    (source : TensorObj K 3) (T : Fin r → TensorObj K 3)
    {ι : Fin r → Fin 3 → Type u}
    (b : (t : Fin r) → (i : Fin 3) → Basis (ι t i) K ((T t).V i))
    (label : (t : Fin r) → (i : Fin 3) → ι t i → CompleteWord ell)
    (beta : Fin r → Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (n : Fin r → ℕ) (hsource : ∀ t, TensorObj.Restrict (T t) source) :
    TensorObj.Restrict
      (TensorObj.kronFin r
        (fun t => restrictedPower (T t) (b t) (label t) (beta t) epsilon (n t)))
      (source.kronPow (∑ t, n t)) := by sorry
