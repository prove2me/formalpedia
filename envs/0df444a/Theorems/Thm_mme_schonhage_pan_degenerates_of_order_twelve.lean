-- Prove2me | Theorems.Thm_mme_schonhage_pan_degenerates_of_order_twelve
-- name    : mme_schonhage_pan_degenerates_of_order_twelve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T03:40:29.15596+00:00
-- url     : https://prove2.me/theorems/814eae1b-bf37-44ef-b0c8-750f7f711ce4
-- title:
--   Pan–Winograd triple direct sum has an order-12, 156-slot degeneration
-- statement:
--   Over every field $K$, the direct sum $\langle1,5,22\rangle \oplus \langle11,2,5\rangle \oplus \langle10,11,1\rangle$ is an order-12 degeneration of the order-three diagonal tensor $I_{156}$. Concretely, there is a polynomial family from the 156 diagonal rank-one slots whose coefficients in degrees 0 through 11 vanish and whose degree-12 coefficient is exactly this three-summand matrix-multiplication tensor. The construction is characteristic-free: its factor coefficients are integers and use no division.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), 73–125, Appendix p. 125 (PDF p. 53), Tables 19.3''–19.8'' and the signed companion rule in Table 19.9; Pan attributes mapping (A2) over an arbitrary field to Schönhage.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
universe u
open MME

theorem mme_schonhage_pan_degenerates_of_order_twelve
    {K : Type u} [Field K] :
    DegeneratesOfOrder
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1])
      (TensorObj.diagObj K 3 156) 12 := by sorry
