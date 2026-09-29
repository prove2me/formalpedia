-- Prove2me | Theorems.Thm_mme_Ctensor_three_star_dimension_products_common_volume
-- name    : mme_Ctensor_three_star_dimension_products_common_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:32:50.488798+00:00
-- url     : https://prove2.me/theorems/9c204a03-4f0b-427e-9633-03e8fdc96305
-- title:
--   Three heterogeneous C-tensor stars retain the common cyclic volume
-- statement:
--   Let $X,Y,Z$ be three possibly different C-tensors over $\langle1,H,1\rangle$.  Suppose every component matrix product in all three tensors has the same volume $v$.  Choose arbitrary length-$R$ component words $x,y,z$.  In the heterogeneous cyclic product $X\otimes\pi(Y)\otimes\pi^2(Z)$, let $a,b,c$ be the three resulting matrix-product dimensions.  Then
--
--   $$
--   abc=v^{3R}.
--   $$
--
--   Thus the cyclic volume calculation uses only the common component volumes; it does not require the three stars, or their fine-coordinate identifications, to be equal.
-- source:
--   The component-volume calculation in Strassen's C-tensor value method, as used by D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneCertificate

open MME BigOperators

universe u

theorem mme_Ctensor_three_star_dimension_products_common_volume
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume R : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (x y z : Fin R → Fin H) :
    let a := ∏ r, certX.m (x r) * certY.p (y r) * certZ.n (z r)
    let b := ∏ r, certX.n (x r) * certY.m (y r) * certZ.p (z r)
    let c := ∏ r, certX.p (x r) * certY.n (y r) * certZ.m (z r)
    a * b * c = volume ^ (3 * R) := by
  sorry
