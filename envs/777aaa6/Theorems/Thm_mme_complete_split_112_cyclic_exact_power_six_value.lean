-- Prove2me | Theorems.Thm_mme_complete_split_112_cyclic_exact_power_six_value
-- name    : mme_complete_split_112_cyclic_exact_power_six_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:19:37.176324+00:00
-- url     : https://prove2.me/theorems/90ae5b9c-48e8-4472-91dc-cf05dccb5011
-- title:
--   Exact three-mode power six-values for the q=5 square 121 and 211 components
-- statement:
--   Let $q = 5$, let $l, g$ be positive integers with $341\,l < 100\,g$, and let $e$ be either non-trivial cyclic permutation of the three modes, so that the rotated block shape is $\rho(i) = \mathrm{cwSquareBlockType}(1,1,2)(e^{-1}i)$ — that is, the $121$ and $211$ orientations of the canonical coupled square block.
--
--   Then for every $\tau$ there is a complete-split profile family $\beta$, with probabilities exactly $\mathrm{profileProbability}\big(l/(2(l+g))\big)$, such that the **exact** three-mode power of the rotated block,
--
--   $$\mathrm{restrictedPower}_K\big(5, \rho, \beta \circ e^{-1}, 0, N\big), \qquad N = 2(l+g)m,$$
--
--   has six-symmetrized restriction rate at least $\exp(\mathrm{rateLog}/3)$, with
--
--   $$\mathrm{rateLog} \;=\; \log 2 \cdot H\big(\beta_2\big) \;+\; 2\log 2 \;+\; 3\tau\,\frac{2g+l}{l+g}\,\log 5 .$$
--
--   The rate is the same as in the unrotated orientation: rotating the modes permutes the profiles but neither the entropy of the retained mode nor the matrix volume changes.
--
--   This is the companion of `mme_complete_split_112_cyclic_prescribedZ_six_value` one restriction earlier in its own proof. That argument extracts matrix multiplication into the six-symmetrization of the star family, transports it through the cyclic orbit isomorphism to the rotated exact-profile power, and only then forgets down to the prescribed Z power of the rotated block. The statement here stops at the exact-profile power, which is what a consumer needs when all three mode profiles of a cell are pinned rather than only the Z histogram.
-- source:
--   Duan, Wu, and Zhou / Coppersmith-Winograd coupled square family; the exact-profile form of the accepted prescribed-Z endpoint, taken at the point where its own proof builds the C-tensor family certificate. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . Supporting lemma: no asymptotic exponent claim.

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_permutation

open MME MME.CompleteSplit MME.CompleteSplit112
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_cyclic_exact_power_six_value
    {K : Type u} [Field K]
    (l g : ℕ) (hbalance : 341 * l < 100 * g)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (tau : ℝ) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma,
        (beta mode).probability sigma =
          (profileProbability
            ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      let rho : Fin 3 → Fin 5 :=
        fun i ↦ cwSquareBlockType 1 1 2 (e.symm i)
      let rateLog : ℝ :=
        Real.log 2 * mme_modern_entropyBits (beta 2).probability +
          2 * Real.log 2 +
          3 * tau *
            (((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5)
      HasSixSequenceRate TensorObj.Restrict
        (fun m ↦ MME.CompleteSplitCanonicalSquare.restrictedPower K 5 rho
          (fun i ↦ beta (e.symm i)) 0 (2 * ((l + g) * m)))
        (fun m ↦ 2 * ((l + g) * m)) tau
        (Real.exp (rateLog / 3)) := by sorry
