-- Prove2me | Definitions.Def_coupledQ6OrientedSurvivor
-- name    : coupledQ6OrientedSurvivor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T18:16:51.847027+00:00
-- url     : https://prove2.me/theorems/a007ac39-a979-4903-87ad-8fce61252ca0
-- title:
--   One oriented coupled $q=6$ survivor
-- statement:
--   For a field $K$ and nonnegative integers $L,G$, define the oriented retained block
--
--   $$
--   S^{\mathrm{or}}_{L,G}=\langle 6,1,6\rangle_K^{\otimes 2G}\otimes\langle 1,6,1\rangle_K^{\otimes 2L}.
--   $$
--
--   This is the fine tensor carried by one exact-profile block before taking the three cyclic orientations. Its cyclic product is the coupled $q=6$ survivor used in the Coppersmith--Winograd extraction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--272, especially the retained constituent products on pp. 270--271.

import Definitions.Def_mme_CW_q6_coupled_survivor

/-!
# One oriented coupled q=6 survivor

Before cyclic symmetrization, one retained exact-profile block has `2*G`
copies of the high constituent and `2*L` copies of the low constituent.
The cyclic product of this oriented block is the coupled q=6 survivor.
-/

universe u

namespace MME

noncomputable def coupledQ6OrientedSurvivor
    (K : Type u) [Field K] (L G : ℕ) : TensorObj K 3 :=
  TensorObj.kron
    ((MMObj K 6 1 6).kronPow (2 * G))
    ((MMObj K 1 6 1).kronPow (2 * L))

end MME


