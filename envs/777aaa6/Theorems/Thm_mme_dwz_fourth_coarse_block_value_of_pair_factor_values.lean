-- Prove2me | Theorems.Thm_mme_dwz_fourth_coarse_block_value_of_pair_factor_values
-- name    : mme_dwz_fourth_coarse_block_value_of_pair_factor_values
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:23:32.304089+00:00
-- url     : https://prove2.me/theorems/6f8d963d-d749-47d3-81b3-21ab8cbbf938
-- title:
--   Fourth-power coarse-block value from a pair of square constituent values
-- statement:
--   **Component values of the fourth power, assembled from a pair of square components.**
--
--   Work over a field $K$ and fix the Coppersmith--Winograd parameter $q$.  The tensor square
--   $CW_q^{\otimes 2}$ carries a fifteen-shape decomposition, each shape $s$ recording a triple of
--   per-mode grades $(\mathrm{shapeX}(s), \mathrm{shapeY}(s), \mathrm{shapeZ}(s))$; the fourth power
--   $CW_q^{\otimes 4}$ carries the coarser nine-grade decomposition indexed by
--   $\sigma = (\sigma_0, \sigma_1, \sigma_2)$.
--
--   Let $p = (p_1, p_2)$ be a pair of square shapes that is *compatible* with $\sigma$, meaning the
--   grades add mode by mode:
--
--   $$\mathrm{shapeX}(p_1) + \mathrm{shapeX}(p_2) = \sigma_0, \qquad
--     \mathrm{shapeY}(p_1) + \mathrm{shapeY}(p_2) = \sigma_1, \qquad
--     \mathrm{shapeZ}(p_1) + \mathrm{shapeZ}(p_2) = \sigma_2 .$$
--
--   Let $X$ and $Y$ be tensors restricting to the square blocks of shapes $p_1$ and $p_2$
--   respectively, and suppose each has a strict value endpoint at exponent $\tau$: $X$ has tau-value
--   at least $V$ for every $0 \le V < e_X$, and $Y$ has tau-value at least $V$ for every
--   $0 \le V < e_Y$, with $e_X, e_Y > 0$.  Then the fourth-power coarse block of grade $\sigma$ has
--   tau-value at least $W$ for every
--
--   $$0 \le W < e_X \, e_Y .$$
--
--   This is the *analysis of component values* of the fourth-power laser method: the fine-to-coarse
--   restriction says that the coarse block of grade $\sigma$ dominates the Kronecker product of any
--   compatible pair of fine square constituents, and values are multiplicative under Kronecker
--   products, so every compatible pair contributes a lower bound $e_X e_Y$ on the value of the coarse
--   block.  Taking the best pair over all decompositions of $\sigma$ is what turns the known square
--   component values into the fourth-power component values that the global entropy optimisation then
--   consumes.
--
--   *Formalization note.* The two inputs are `mme_dwz_fourth_pair_factor_restrictions_to_coarse`, which
--   produces the restriction of `TensorObj.kron X Y` into the coarse block, and
--   `mme_HasTauValueAtLeast_kron_of_each_strict_below_product`, the binary multiplicativity of the
--   tau-value; the value then transports along the restriction by
--   `mme_HasTauValueAtLeast_mono_restrict`.  Endpoints are kept in strict form throughout, since no
--   step of the extraction ever produces a value *at* an endpoint.
-- source:
--   R. Duan, H. Wu and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Section 3.5 (fine-to-coarse constituent restrictions) and Section 2.4 (multiplicativity of values); arXiv:2210.10173.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_coarse_block_value_of_pair_factor_values
    {K : Type u} [Field K] (q : ℕ) (p : Fin 15 × Fin 15)
    (sigma : Fin 3 → Fin 9)
    (hx : (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val = (sigma 0).val)
    (hy : (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val = (sigma 1).val)
    (hz : (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val = (sigma 2).val)
    {X Y : TensorObj K 3}
    (hX : TensorObj.Restrict X
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1))))
    (hY : TensorObj.Restrict Y
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2))))
    (tau eX eY : ℝ) (heX : 0 < eX) (heY : 0 < eY)
    (hXv : ∀ V : ℝ, 0 ≤ V → V < eX → HasTauValueAtLeast X tau V)
    (hYv : ∀ V : ℝ, 0 ≤ V → V < eY → HasTauValueAtLeast Y tau V) :
    ∀ W : ℝ, 0 ≤ W → W < eX * eY →
      HasTauValueAtLeast
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor sigma)
        tau W := by
  sorry
