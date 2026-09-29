-- Prove2me | Theorems.Thm_mme_graded_integer_regional_scaled_step_certified_rate
-- name    : mme_graded_integer_regional_scaled_step_certified_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:55:00.708838+00:00
-- url     : https://prove2.me/theorems/77c611cd-4037-449e-b99c-18291ac7dfbf
-- title:
--   Scaled graded-source regional steps have certified rate close to the regional rate
-- statement:
--   This is the graded-source form of the scaled integer regional step. Fix integer regional data at level ell whose parent counts are positive and whose split counts, complete-word histograms, mass, support and boundary-profile conditions are as for integer steps. Let c be strictly below the regional rate. Then, for all sufficiently large t, the following holds for every target address of the t-scaled split counts and every source predicate S that contains the flattening of each word which is both parent-graded and typical for the t-scaled data (at tolerance sqrt(8*25*R*|W|^2*(floor(sqrt t)+2)/t)): there is a graded-source integer step with source S whose output is the graded, useful projection at the given address, and whose certified logarithmic copy count is at least c*t. Here parent-graded means that, in every parent occurrence, the two halves' grades add up to the parent's grade. Such a source can be the whole-interface output of an earlier exact stage, which is what lets constituent stages chain (More Asymmetry, Theorem 6.4 and Algorithm 1).
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3, Theorem 6.4, Section 6.6 and Algorithm 1.

import Mathlib
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
set_option autoImplicit false

theorem mme_graded_integer_regional_scaled_step_certified_rate {ell R : ℕ}
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
        (∀ i x, ParentGraded parent (fun r ↦ t * n r) i (ProfiledCW.split (positionsAt n t) rfl x) →
          parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
          (fun c w ↦ t * mu i c w)
          (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
            ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
          (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : IntegerStepG ell (lenAt n t * 2 ^ (ell - 1)) S,
          D.step.output = (fun i x ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl x) ∧
            Useful (fullCell htotal a) (fun c w ↦ t * mu i c w)
              (ProfiledCW.split (positionsAt n t) rfl x)) ∧
          c * t ≤ D.step.certifiedLogCopies := by sorry
