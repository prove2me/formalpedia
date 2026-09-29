-- Prove2me | Theorems.Thm_mme_prescribed_product_alphabet_word_card
-- name    : mme_prescribed_product_alphabet_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:19:22.022065+00:00
-- url     : https://prove2.me/theorems/83ae6dae-305a-4c44-90ef-94225a3969ff
-- title:
--   Exact prescribed-histogram word count over a product alphabet
-- statement:
--   Let a finite alphabet $I$ be identified with $[H]\times[V]$, with its grade equal to the first coordinate. Fix a word length $n$ and any prescribed grade histogram $c:[H]\to\mathbb N$. Then
--
--   $$
--   \#\{w\in I^n:\#w^{-1}(h)=c(h)\}
--   =\#\{g\in[H]^n:\#g^{-1}(h)=c(h)\}\,V^n.
--   $$
--
--   The identity remains valid when the prescribed counts are inconsistent with $n$: both constrained word sets are then empty. This form avoids imposing an unnecessary divisibility equation on the tensor-power length.
-- source:
--   Elementary product-alphabet counting identity; applied to prescribed split histograms in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3.

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Data.Finite.Card

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_prescribed_product_alphabet_word_card
    {I : Type u} [Fintype I] [DecidableEq I]
    (H V n : ℕ) (counts : Fin H → ℕ) (grade : I → Fin H)
    (letter : I ≃ Fin H × Fin V)
    (hletter : ∀ i, grade i = (letter i).1) :
    Nat.card
        {w : MME.DWZComponentRestriction.PowIndex I n //
          ∀ h, Fintype.card
              {r : Fin n // grade
                (MME.DWZComponentRestriction.PowIndex.get n w r) = h} =
                  counts h} =
      Nat.card
          {g : Fin n → Fin H //
            ∀ h, Fintype.card {r : Fin n // g r = h} = counts h} *
        V ^ n := by
  sorry
