-- Prove2me | solution 1 for MarkoffTransfer.mLevel_strict
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:16:28.493562+00:00
-- url     : https://prove2.me/submissions/123c411c-8566-4a33-83a3-7157c9d5e30f

import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
open MarkoffTransfer in
theorem solution : ∀ (n : ℕ), ∀ t ∈ mLevel n, StrictM t := by
  have hroot : StrictM mRoot := by
    unfold StrictM mRoot IsMarkoff markoffForm
    norm_num
  have hchildL : ∀ t : ℤ × ℤ × ℤ, StrictM t → StrictM (childL t) := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold IsMarkoff markoffForm at h5
    simp only at h5
    unfold StrictM childL
    simp only
    refine ⟨by omega, by omega, by nlinarith, by nlinarith, ?_⟩
    unfold IsMarkoff markoffForm
    linear_combination h5
  have hchildR : ∀ t : ℤ × ℤ × ℤ, StrictM t → StrictM (childR t) := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold IsMarkoff markoffForm at h5
    simp only at h5
    unfold StrictM childR
    simp only
    refine ⟨by omega, by omega, by nlinarith, by nlinarith, ?_⟩
    unfold IsMarkoff markoffForm
    linear_combination h5
  have hstrict : ∀ w : List Bool, StrictM (mEval w) := by
    intro w
    induction w with
    | nil => exact hroot
    | cons b w ih =>
      cases b with
      | false => exact hchildL _ ih
      | true => exact hchildR _ ih
  have hparL : ∀ t : ℤ × ℤ × ℤ, StrictM t → mParent (childL t) = t := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold mParent childL
    simp only
    rw [show 3 * a * c - (3 * a * c - b) = b from by ring, if_neg (by omega : ¬ b ≤ a)]
  have hparR : ∀ t : ℤ × ℤ × ℤ, StrictM t → mParent (childR t) = t := by
    rintro ⟨a, b, c⟩ h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold mParent childR
    simp only
    rw [show 3 * b * c - (3 * b * c - a) = a from by ring, if_pos (by omega : a ≤ b)]
  have hne : ∀ t : ℤ × ℤ × ℤ, StrictM t → childL t ≠ childR t := by
    rintro ⟨a, b, c⟩ h hEq
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only at h1 h2 h3 h4
    unfold childL childR at hEq
    simp only [Prod.mk.injEq] at hEq
    omega
  have hlevel : ∀ n : ℕ, ∀ t ∈ mLevel n, StrictM t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [show mLevel 0 = {mRoot} from rfl, Finset.mem_singleton] at ht
      rw [ht]
      exact hroot
    | succ n ih =>
      intro t ht
      rw [show mLevel (n + 1) = (mLevel n).image childL ∪ (mLevel n).image childR from rfl,
        Finset.mem_union] at ht
      rcases ht with ht | ht
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        exact hchildL s (ih s hs)
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        exact hchildR s (ih s hs)
  exact hlevel
