-- Prove2me | Theorems.Thm_mme_sixSymmetrization_restrict
-- name    : mme_sixSymmetrization_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:40:13.775542+00:00
-- url     : https://prove2.me/theorems/47a9c793-adfa-4494-b86a-0d25a571a84c
-- title:
--   Tensor restriction is preserved by DWZ six-symmetrization
-- statement:
--   Let $X$ and $Y$ be order-three tensors over a field, with $X$ a restriction of $Y$. Form the Duan--Wu--Zhou full symmetrization by multiplying the three cyclic mode permutations and then multiplying by its first-two-mode swap. Then the full symmetrization of $X$ is a restriction of the full symmetrization of $Y$. This lets a tensor extraction proved in one asymmetric orientation be lifted to the six-symmetrized construction used by the final value bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3, arXiv:2210.10173v5.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_restrict
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (sixSymmetrization X) (sixSymmetrization Y) := by
  sorry
