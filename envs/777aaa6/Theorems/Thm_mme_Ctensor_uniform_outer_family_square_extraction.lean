-- Prove2me | Theorems.Thm_mme_Ctensor_uniform_outer_family_square_extraction
-- name    : mme_Ctensor_uniform_outer_family_square_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:14:58.999244+00:00
-- url     : https://prove2.me/theorems/afa04ad1-0c5f-4ca9-b112-4723cba5bd29
-- title:
--   Uniform square extraction from an outer family of stars
-- statement:
--   Let $T$ be a tensor over a field $K$ admitting a shared-mode star family certificate with $A$ outer stars and $H>0$ leaves per star. Suppose every leaf has matrix dimensions $(m,n,p)$. The cyclic symmetrization of $T$ restricts to a direct sum of $k$ copies of $\langle mnp,mnp,mnp\rangle$, where
--
--   $$k\ge A^3H^2\exp\!\left(-100\sqrt{\log(H+1)}\right).$$
--
--   This combines square-block extraction across all outer triples while preserving the common matrix dimensions and the finite count bound.
-- source:
--   Uniform three-star Behrend extraction, prefix selection, and distribution of cyclic symmetrization over the outer direct sum.

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_CTensorOneHOneFamilyCertificate
open MME
universe u
set_option autoImplicit false

theorem mme_Ctensor_uniform_outer_family_square_extraction
    {K : Type u} [Field K] {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (m n p : ℕ)
    (hdims : ∀ a h, (stars.certificate a).m h = m ∧
      (stars.certificate a).n h = n ∧ (stars.certificate a).p h = p)
    (hH : 0 < H) :
    ∃ k : ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K (m * n * p) (m * n * p) (m * n * p)))
        (cyclicSymmetrization T) ∧
      (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) ≤ (k : ℝ) := by sorry
