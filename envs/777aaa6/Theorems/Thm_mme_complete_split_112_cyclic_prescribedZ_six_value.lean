-- Prove2me | Theorems.Thm_mme_complete_split_112_cyclic_prescribedZ_six_value
-- name    : mme_complete_split_112_cyclic_prescribedZ_six_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:06:50.497532+00:00
-- url     : https://prove2.me/theorems/3d52fdd1-5cdb-446a-8066-fb55fbbda1df
-- title:
--   Prescribed-Z six-values for the q=5 square 121 and 211 components
-- statement:
--   Let $T$ be either literal cyclic orientation $T_{121}$ or $T_{211}$ of the canonical square $(1,1,2)$ component of $\mathrm{CW}_5^{\otimes2}$ over an arbitrary field. For nonnegative integers $l,g$ satisfying $341l<100g$, prescribe Z-split counts $(l+g,l+g,0)$ with denominator $D=2(l+g)$. Put $r=l/(2(l+g))$ and let $h$ be the natural-log entropy of $(r,1-2r,r)$.
--
--   For every real $\tau$, the prescribed-Z six-symmetric restriction value has the lower certificate
--   $$
--   \exp\!\left(\frac{h+2\log 2}{3}
--   +\tau\frac{2g+l}{l+g}\log 5\right).
--   $$
--
--   The certificate gives actual MM direct-sum restrictions at arbitrarily large compatible indices and physical lengths, for every positive strict lower base. The prescribed profile is the uniform directional profile of the rotated source, while the value uses the internal $(1,1,2)$ parameter $r$. This makes the cyclic components available to the DWZ recursion without discarding their Z-split constraints.
--
--   **Formalization Note** The source uses the literal canonical block basis, and the theorem returns the normalized complete profiles. It does not identify a cyclically permuted star with an unpermuted star carrying the same distinguished shared mode.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Equation (3), Lemma 4.6(d) and its Appendix A proof, with cyclic transport of the complete profiles. Rational-profile q=5 finite restriction certificate under the proved directional-rate theorem's arithmetic balance hypothesis.

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

theorem mme_complete_split_112_cyclic_prescribedZ_six_value
    {K : Type u} [Field K]
    (l g : ℕ) (hbalance : 341 * l < 100 * g)
    (e : Equiv.Perm (Fin 3))
    (he : e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm)
    (p : IntegerZSplitProfile 3)
    (hden : p.denominator = 2 * (l + g))
    (hcount : p.count = ![l + g, l + g, 0])
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
      HasPrescribedZSixRestrictionValueAtLeast
        (MME.CompleteSplitCanonicalSquare.obj K 5 rho)
        (MME.CompleteSplitCanonicalSquare.basis K 5 rho 2)
        (fun x ↦
          (MME.CompleteSplitCanonicalSquare.label 5 rho 2 x) 0)
        p tau (Real.exp (rateLog / 3)) := by sorry
