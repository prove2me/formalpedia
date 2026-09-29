-- Prove2me | Theorems.Thm_mme_Ctensor_cyclic_dimension_products_common_volume
-- name    : mme_Ctensor_cyclic_dimension_products_common_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:24:47.686488+00:00
-- url     : https://prove2.me/theorems/c68290e4-3dde-4fba-b6e6-0be5f178d499
-- title:
--   Cyclic C-tensor dimension products have the common cubed volume
-- statement:
--   Let the components of a C-tensor have dimensions $(m_h,n_h,p_h)$ and common volume $m_hn_hp_h=v$. For three component words $x,y,z$ of length $R$, define the cyclic product dimensions
--
--   $$
--   A=\prod_r m_{x_r}p_{y_r}n_{z_r},\quad
--   B=\prod_r n_{x_r}m_{y_r}p_{z_r},\quad
--   C=\prod_r p_{x_r}n_{y_r}m_{z_r}.
--   $$
--
--   Then $ABC=v^{3R}$. This is the common-volume calculation for complete blocks in the cyclic C-tensor construction; it requires no equality of the individual component dimensions.
-- source:
--   Cyclic common-volume calculation in Strassen's C-tensor method, as used by Coppersmith and Winograd (1990), journal pp. 271--272.

import Definitions.Def_CTensorOneHOneCertificate

open MME BigOperators

universe u

theorem mme_Ctensor_cyclic_dimension_products_common_volume
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume R : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (x y z : Fin R → Fin H) :
    let a := ∏ r, cert.m (x r) * cert.p (y r) * cert.n (z r)
    let b := ∏ r, cert.n (x r) * cert.m (y r) * cert.p (z r)
    let c := ∏ r, cert.p (x r) * cert.n (y r) * cert.m (z r)
    a * b * c = volume ^ (3 * R) := by
  sorry
