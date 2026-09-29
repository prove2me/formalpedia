-- Prove2me | Theorems.Thm_mme_complete_split_112_exact_power_six_value
-- name    : mme_complete_split_112_exact_power_six_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:14:25.522851+00:00
-- url     : https://prove2.me/theorems/42a825fa-210f-4059-b791-8f42bc048637
-- title:
--   Exact three-mode power six-value of the canonical q=5 square 112 component
-- statement:
--   Let $q = 5$ and let $l, g$ be positive integers with $341\,l < 100\,g$, the balance condition of the coupled square family. Write $\beta$ for the complete-split profile family determined by the parameter $p = l/(2(l+g))$, and consider the **exact** three-mode power
--
--   $$\mathrm{restrictedCanonicalPower}_K(5, \beta, 0, N), \qquad N = 2(l+g)m,$$
--
--   that is, the projection of $\mathrm{CW}_5^{\otimes N}$ onto the words whose profile in each of the three modes is exactly $\beta$ (tolerance $\varepsilon = 0$).
--
--   Then for every $\tau$ there is such a $\beta$, with probabilities exactly $\mathrm{profileProbability}(p)$, for which the six-symmetrized restriction rate of that exact power is at least $\exp(\mathrm{rateLog}/3)$, where
--
--   $$\mathrm{rateLog} \;=\; \log 2 \cdot H\big(\beta_2\big) \;+\; 2\log 2 \;+\; 3\tau\,\frac{2g+l}{l+g}\,\log 5 ,$$
--
--   with $H$ the binary entropy of the third mode's profile. Concretely: for every base strictly below $\exp(\mathrm{rateLog}/3)$ and every cutoff, some multiplicity $m$ beyond the cutoff admits an actual finite direct sum of matrix-multiplication tensors restricting from the six-symmetrization of that exact power, with total $\tau$-weight at least the base raised to $6N$.
--
--   This is the companion of `mme_complete_split_112_prescribedZ_six_value` **one step earlier in its own proof**. That theorem's argument first builds a C-tensor family certificate on this exact-profile power and only afterwards forgets down to the prescribed Z-split power. Consumers that must value an exact three-mode cell — for instance a cell of a recursive block decomposition, where all three mode profiles are pinned, not just the Z histogram — need this earlier form, which is strictly stronger for that purpose and cannot be recovered from the prescribed-Z statement.
-- source:
--   Duan, Wu, and Zhou / Coppersmith-Winograd coupled square family; the exact-profile form of the accepted prescribed-Z endpoint, taken at the point where its own proof builds the C-tensor family certificate. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . Supporting lemma: no asymptotic exponent claim.

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data

open MME MME.CompleteSplit MME.CompleteSplit112
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_exact_power_six_value
    {K : Type u} [Field K]
    (l g : ℕ) (hbalance : 341 * l < 100 * g)
    (tau : ℝ) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma,
        (beta mode).probability sigma =
          (profileProbability
            ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      let rateLog : ℝ :=
        Real.log 2 * mme_modern_entropyBits (beta 2).probability +
          2 * Real.log 2 +
          3 * tau *
            (((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5)
      HasSixSequenceRate TensorObj.Restrict
        (fun m ↦ restrictedCanonicalPower K 5 beta 0 (2 * ((l + g) * m)))
        (fun m ↦ 2 * ((l + g) * m)) tau
        (Real.exp (rateLog / 3)) := by sorry
