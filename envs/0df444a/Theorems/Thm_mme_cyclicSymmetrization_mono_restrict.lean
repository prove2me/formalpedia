-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
-- name    : mme_cyclicSymmetrization_mono_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:45:59.354564+00:00
-- url     : https://prove2.me/theorems/52468eac-ab99-4819-9b87-99e2334170b6
-- title:
--   Cyclic symmetrization preserves tensor restriction
-- statement:
--   Let $X$ and $Y$ be order-three tensors over a field, and suppose $X$ is a restriction of $Y$. Write $\pi$ for the cyclic permutation of the three tensor modes. Then the modewise maps witnessing $X\leq Y$, together with their two cyclic relabelings, witness
--
--   $$
--   X\otimes\pi(X)\otimes\pi^2(X)
--   \;\leq_{\mathrm{Restrict}}\;
--   Y\otimes\pi(Y)\otimes\pi^2(Y).
--   $$
--
--   Thus cyclic symmetrization is monotone for Strassen restriction. This is the structural bridge that transports every concrete block selected inside the coupled Coppersmith--Winograd constituent into the cyclic tensor used by its symmetric value.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), definition of symmetric value by cyclic tensor product on journal p. 264 (PDF p. 14); restriction functoriality is the standard tensor-map naturality used there; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_cyclicSymmetrization_mono_restrict
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (cyclicSymmetrization X) (cyclicSymmetrization Y) := by sorry
