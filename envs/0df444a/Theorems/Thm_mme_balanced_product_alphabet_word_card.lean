-- Prove2me | Theorems.Thm_mme_balanced_product_alphabet_word_card
-- name    : mme_balanced_product_alphabet_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:47:19.377492+00:00
-- url     : https://prove2.me/theorems/af390a51-9721-4f34-ad97-b1b297f42ccb
-- title:
--   Exact count of balanced words over a product alphabet
-- statement:
--   Let a finite alphabet $I$ be identified with the product $[H]\times[V]$, and suppose its grade map is exactly the first coordinate. Consider words of length $Hm$ in which every one of the $H$ grades occurs exactly $m$ times. Their number is
--
--   $$
--   \#\{\text{balanced }I\text{-words}\}
--   =\#\{\text{balanced }[H]\text{-grade words}\}\,V^{Hm}.
--   $$
--
--   The factor $V^{Hm}$ records the independent within-grade label at every word position. The theorem uses the recursive word representation employed by tensor powers, but the count is the ordinary finite product-alphabet identity.
-- source:
--   Elementary product-alphabet counting identity; applied to the equal-multiplicity rectangular component values in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Table 2.

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Data.Finite.Card

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_balanced_product_alphabet_word_card
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V m : ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    Nat.card
        {w : MME.DWZComponentRestriction.PowIndex I (H * m) //
          ∀ h, Fintype.card
              {r : Fin (H * m) // grade
                (MME.DWZComponentRestriction.PowIndex.get _ w r) = h} = m} =
      Nat.card
          {g : Fin (H * m) → Fin H //
            ∀ h, Fintype.card {r : Fin (H * m) // g r = h} = m} *
        V ^ (H * m) := by
  sorry
