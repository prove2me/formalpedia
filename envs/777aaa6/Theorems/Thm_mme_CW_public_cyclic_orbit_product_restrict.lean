-- Prove2me | Theorems.Thm_mme_CW_public_cyclic_orbit_product_restrict
-- name    : mme_CW_public_cyclic_orbit_product_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:25:45.96922+00:00
-- url     : https://prove2.me/theorems/64397f67-16e4-4680-9f48-4751a742543a
-- title:
--   Assemble the three rotated coupled CW blocks
-- statement:
--   Let $T_{112}$ be the coupled constituent of the square of the Coppersmith--Winograd tensor, and let $T_{211}$ and $T_{121}$ be its two cyclic mode rotations. If three source blocks respectively restrict to these three constituents, then their Kronecker product restricts to the canonical cyclic product
--
--   $$T_{112} \otimes T_{211} \otimes T_{121}.$$
--
--   This packages the functorial assembly step used for the coupled cyclic orbit in the five-grading of $T_q \otimes T_q$; the separate block-identification lemmas supply its three hypotheses.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), cyclic symmetrization on p. 264 and the three coupled tensor-square constituents in equation (11), cases (d), pp. 265--266.

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation

open MME

universe u

theorem mme_CW_public_cyclic_orbit_product_restrict
    {K : Type u} [Field K] (q : ℕ)
    {B112 B211 B121 : TensorObj K 3}
    (h112 : TensorObj.Restrict (coupledObj K q) B112)
    (h211 : TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (coupledObj K q)) B211)
    (h121 : TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)) B121) :
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (coupledObj K q))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))))
      (TensorObj.kron B112 (TensorObj.kron B211 B121)) := by sorry
