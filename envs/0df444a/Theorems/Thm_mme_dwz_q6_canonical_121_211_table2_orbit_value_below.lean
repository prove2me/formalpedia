-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_211_table2_orbit_value_below
-- name    : mme_dwz_q6_canonical_121_211_table2_orbit_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:20:00.101386+00:00
-- url     : https://prove2.me/theorems/357b1bab-d7fe-428c-bf13-4c75fb886972
-- title:
--   Table-2 value on the canonical $112\otimes211\otimes121$ orbit
-- statement:
--   Fix $q=6$ and $3\tau\ge2$. For every nonnegative $V$ strictly below the common Table-2 base of the rotated coupled constituents,
--
--   $$
--   V<2^{2/3}6^{\tau}\bigl(6^{3\tau}+2\bigr)^{1/3},
--   $$
--
--   the literal canonical orbit
--
--   $$
--   T_{112}\otimes T_{211}\otimes T_{121}
--   $$
--
--   has tau-value at least $V^3$. The three factors are the actual canonical graded blocks, with $211$ and $121$ obtained by the two cyclic rotations of the coupled Coppersmith--Winograd tensor. The strict inequality is the rate-correct asymptotic form that absorbs the source's subexponential extraction loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6(d), Section 6.3 and Table 2, shapes (1,2,1) and (2,1,1), PDF pp. 32-33 and 59-60; https://arxiv.org/abs/2210.10173. The cyclic coupled-tensor extraction is the construction of Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, JSC 9 (1990), pp. 270-272.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_public_cyclic_orbit_product_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_dwz_q6_121_211_componentBase_cube

open MME MME.DWZSquare

set_option autoImplicit false

universe u

theorem mme_dwz_q6_canonical_121_211_table2_orbit_value_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (13 : Fin 15)) :
    HasTauValueAtLeast
      (TensorObj.kron
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 1 1 2))
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 2 1 1))
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 1 2 1))))
      tau (V ^ (3 : ℕ)) := by sorry
