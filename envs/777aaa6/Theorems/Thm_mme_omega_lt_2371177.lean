-- Prove2me | Theorems.Thm_mme_omega_lt_2371177
-- name    : mme_omega_lt_2371177
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T22:07:41.889599+00:00
-- url     : https://prove2.me/theorems/0f6f3856-1b27-46de-91a4-d4ea012b4cd3
-- title:
--   Matrix Multiplication Exponent < 2.371177
-- statement:
--   For every field $K$, the matrix multiplication exponent satisfies $\omega_K < 2.371177$.

import Definitions.Def_mme_omega
universe u
open MME

theorem mme_omega_lt_2371177 {K : Type u} [Field K] :
    matMulExp K < 2371177 / 1000000 := by sorry
