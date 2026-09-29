-- Prove2me | Theorems.Thm_mme_integer_regional_scaled_step_certified_rate
-- name    : mme_integer_regional_scaled_step_certified_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:12:07.929994+00:00
-- url     : https://prove2.me/theorems/82311ae1-980f-4eeb-bb15-02a8c9c4c5a3
-- title:
--   Scaled integer regional steps have certified rate arbitrarily close to the regional rate
-- statement:
--   Scaled integer regional steps at any level. Fix integer regional data at level ell: parent types, positive parent counts n, split counts m, and complete-word histograms mu satisfying the mass, support and boundary-profile conditions, and let c be strictly below the regional rate of the data. Then for all sufficiently large t, for every target address of the t-scaled split counts and every source predicate containing the typical band of the t-scaled data at tolerance sqrt(8*25*R*|W|^2*(floor(sqrt t)+2)/t), there is an integer step with that source whose output is the graded, useful projection at the given address, and whose certified logarithmic copy count is at least c*t. This is the finite-length form of the constituent stage rate of More Asymmetry (Theorem 6.4, Section 6.6): all entropy-continuity, Salem-Spencer, polynomial and hole-repair losses are o(t).
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3, Theorem 6.4 and Section 6.6.

import Mathlib
import Definitions.Def_mme_regional_certified_log_copy_bound
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
set_option autoImplicit false

theorem mme_integer_regional_scaled_step_certified_rate {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (c : ℝ) (hc : c < regionalRate htotal n m mu) :
    ∀ᶠ t : ℕ in atTop,
      ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ t * n r),
        a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c) →
      ∀ S : ProfiledCW.Predicate (lenAt n t * 2 ^ (ell - 1)),
        (∀ i x, parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
          (fun c w ↦ t * mu i c w)
          (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
            ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
          (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : IntegerStep ell (lenAt n t * 2 ^ (ell - 1)) S,
          D.output = (fun i x ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl x) ∧
            Useful (fullCell htotal a) (fun c w ↦ t * mu i c w)
              (ProfiledCW.split (positionsAt n t) rfl x)) ∧
          c * t ≤ D.certifiedLogCopies := by sorry
