-- Prove2me | solution 1 for ChainedLabelWidth.widthOK_iff_no_collision
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:25:14.012034+00:00
-- url     : https://prove2.me/submissions/4b4a7b44-3150-4cc2-bf0a-d92fd6529dda

import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
open ChainedLabelWidth Finset in
theorem solution {A B : ℕ} (hA : 2 ≤ A) (M : ℕ) :
    WidthOK B M ↔
      ∀ a b a' b', a < A → b < B → a' < A → b' < B →
        chain M a b = chain M a' b' → (a, b) = (a', b') := by
  unfold WidthOK chain
  constructor
  · -- a frame at least as wide as the inner alphabet separates labels
    intro hBM a b a' b' _ hb _ hb' h
    have hbM : b < M := lt_of_lt_of_le hb hBM
    have hb'M : b' < M := lt_of_lt_of_le hb' hBM
    have hae : a = a' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : (a + 1) * M ≤ a' * M := Nat.mul_le_mul_right M hlt
        nlinarith
      · have : (a' + 1) * M ≤ a * M := Nat.mul_le_mul_right M hlt
        nlinarith
    subst hae
    have hbe : b = b' := by omega
    rw [hbe]
  · -- a too-narrow frame makes `(0, M)` and `(1, 0)` collide
    intro h
    by_contra hBM
    replace hBM := lt_of_not_ge hBM
    have := h 0 M 1 0 (by omega) hBM (by omega) (by omega) (by ring)
    simp at this
