-- Prove2me | Theorems.Thm_mme_complete_split_exact_power_restrict_prescribedZPower
-- name    : mme_complete_split_exact_power_restrict_prescribedZPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:33:31.401234+00:00
-- url     : https://prove2.me/theorems/5fb56126-a053-4e29-abde-dc3ab8439d0a
-- title:
--   Exact full-profile powers restrict from literal integer-profile prescribed-Z powers
-- statement:
--   Let $T$ be a three-mode tensor over any field, with chosen coordinate bases and complete fine-word labels. Fix an exact full-profile triple $\beta$, a supplied map $s$ from complete words to a finite split-grade alphabet, and an integer Z-split profile $p$ with positive denominator $D$. Suppose the Z full profile pushes forward to this precise integer profile:
--
--   $$
--   p_a=D\sum_{\sigma:s(\sigma)=a}\beta_Z(\sigma)
--   \qquad\text{for every split grade }a.
--   $$
--
--   Then for every natural $m$, the literal all-mode exact complete-profile restriction of $T^{\otimes Dm}$ is a restriction of `prescribedZPower` for the same tensor, the same original Z basis, the split label $x\mapsto s(\operatorname{label}_Z(x))$, and this very profile $p$.
--
--   The source is the single Z-only coordinate projection that keeps exactly the words with $p_a m$ occurrences of each prescribed split grade. X and Y remain unrestricted there; all three complete profiles are enforced only in the output. The compatibility hypothesis is an explicit equality of counts and probabilities, not an assumed tensor restriction or value bound. Power zero and zero profile entries are included.
--
--   For a canonical square component, supply its actual canonical bases and two-letter labels and take $s(\sigma)=\sigma_0$. This gives the literal prescribed-Z source used for 112,121,211 at arbitrary q, and is not limited by the modern balanced-family range. For a higher-level component, the actual half-grade reading map must be supplied. This theorem transfers an existing exact full-profile source construction; it does not itself prove any restricted value, symmetric hashing rate, exact numerical feasibility, or irrational-profile approximation.
-- source:
--   Derived source bridge for Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Definition 3.9 and Equation (3), printed pp. 23–24; square prescribed profiles are discussed in Section 6.3, printed p. 59. Uses the public IntegerZSplitProfile, prescribedZPower, and exact CompleteSplit.restrictedPower definitions without alteration. Histogram pushforward is a finite fiber-count identity. Tensor descent reuses the public theorem mme_restrict_basisZAllowedSubtensor_of_vanishes. The split-reading map and exact compatibility are supplied explicitly; no scalar value or desired extraction is assumed.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZRestrictedValue Module
open scoped BigOperators Classical

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_power_restrict_prescribedZPower
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell) (beta : Fin 3 → Profile ell)
    {t : ℕ} (split : CompleteWord ell → Fin t) (p : IntegerZSplitProfile t)
    (hprofile : ∀ a, (p.count a : ℝ) = (p.denominator : ℝ) *
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
        (beta 2).probability sigma) (m : ℕ) :
    TensorObj.Restrict (restrictedPower T b label beta 0 (p.length m))
      (prescribedZPower T (b 2) (fun x ↦ split (label 2 x)) p m) := by sorry
