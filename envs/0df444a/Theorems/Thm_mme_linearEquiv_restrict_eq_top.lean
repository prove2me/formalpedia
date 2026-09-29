-- Prove2me | Theorems.Thm_mme_linearEquiv_restrict_eq_top
-- name    : mme_linearEquiv_restrict_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:37:45.473476+00:00
-- url     : https://prove2.me/theorems/211487d4-07d1-4c01-ad30-7f552ed1c15c
-- title:
--   Restrict an ambient linear automorphism to a certified full submodule
-- statement:
--   Let $C$ be a linear subspace of a vector space $V$ over a field $K$, and suppose $C$ is certified to equal all of $V$. For every linear automorphism $P : V \simeq_K V$, there is a linear automorphism $E : C \simeq_K C$ whose inclusion into $V$ commutes exactly with $P$: $$\iota_C \circ E = P \circ \iota_C.$$ This is the generic X/Y-mode restriction used when the DWZ component projection certificate identifies those two projected mode spaces with the full component power.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 5.9 (the X/Y component modes are unrestricted while the same variable relabeling acts before and after projection), PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Mathlib.LinearAlgebra.PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_linearEquiv_restrict_eq_top
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (C : Submodule K V) (hC : C = ⊤) (P : V ≃ₗ[K] V) :
    ∃ E : C ≃ₗ[K] C,
      (Submodule.subtype C).comp E.toLinearMap =
        P.toLinearMap.comp (Submodule.subtype C) := by
  sorry
