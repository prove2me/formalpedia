-- Prove2me | Theorems.Thm_mme_graded_integer_regional_band_step_certified_rate
-- name    : mme_graded_integer_regional_band_step_certified_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T16:25:10.307815+00:00
-- url     : https://prove2.me/theorems/c2fa0f18-5520-433f-bc2c-2b454f76f5c7
-- title:
--   Graded integer regional step: uniform certified rate over a histogram band
-- statement:
--   This is the uniform version of the scaled graded integer step rate, over a band of histograms.
--
--   Fix regional data at level `ell`: parent types, positive parent counts `n`, split counts `m` summing to `n`, and complete-word histograms `mu` with the mass condition. Let `c` be any number below the regional rate of `(n, m, mu)`.
--
--   Then there is a relative band width `eta > 0` with the following property, for all sufficiently large scales `t`. Take any histogram `mu'` such that
--   - it has the scaled cell totals of `t * mu`,
--   - every entry is within `eta` times its cell total of `t * mu`, and
--   - it satisfies the support and boundary-profile conditions.
--
--   Take also any target address for the scaled split counts, and any source containing every parent-graded word that is typical for `mu'` at the tight tolerance. Then there is a graded-source integer step for that source with the following properties:
--   - its output is the graded, useful projection at the address for `mu'`;
--   - it has at least `c * t` certified logarithmic copies.
--
--   This is what lets a hashing stage follow an exact stage that splits its interface by histogram type. Every type in the band gets its own step, all at the same rate.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), section 6: uniform rate of the regional hashing step over histogram types near the prescribed distribution. Exact asymptotic statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
set_option autoImplicit false

theorem mme_graded_integer_regional_band_step_certified_rate {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (c : ℝ) (hc : c < regionalRate htotal n m mu) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℕ in atTop,
      ∀ mu' : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ,
        (∀ i c, ∑ w, mu' i c w = ∑ w, t * mu i c w) →
        (∀ i c w, |(mu' i c w : ℝ) - ((t * mu i c w : ℕ) : ℝ)| ≤
          η * ((∑ z, t * mu i c z : ℕ) : ℝ)) →
        (∀ i c w, 0 < mu' i c w → ∑ h, (w h).val = (c.2.val i).val) →
        BoundaryProfiles mu' →
      ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ t * n r),
        a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c) →
      ∀ S : ProfiledCW.Predicate (lenAt n t * 2 ^ (ell - 1)),
        (∀ i x, ParentGraded parent (fun r ↦ t * n r) i (ProfiledCW.split (positionsAt n t) rfl x) →
          parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c) (mu' i)
          (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
            ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
          (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : IntegerStepG ell (lenAt n t * 2 ^ (ell - 1)) S,
          D.step.output = (fun i x ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl x) ∧
            Useful (fullCell htotal a) (mu' i) (ProfiledCW.split (positionsAt n t) rfl x)) ∧
          c * t ≤ D.step.certifiedLogCopies := by sorry
