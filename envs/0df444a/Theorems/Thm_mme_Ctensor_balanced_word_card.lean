-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_word_card
-- name    : mme_Ctensor_balanced_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:00:18.680695+00:00
-- url     : https://prove2.me/theorems/7725e95f-898a-440e-98fb-c6e43cff1aee
-- title:
--   Exact cardinality of a balanced C-tensor type class
-- statement:
--   Fix $H,m\ge0$. Consider words of length $Hm$ over an $H$-letter alphabet in which every letter appears exactly $m$ times. Their number is the multinomial coefficient
--
--   $$
--   \frac{(Hm)!}{(m!)^H}.
--   $$
--
--   This is the exact balanced type class used in Strassen's C-tensor argument. In the $m$-fold type extraction, choosing the same empirical distribution in the three cyclic orientations makes every fine matrix-product block square while retaining $H^{Hm-o(Hm)}$ words.
-- source:
--   Multinomial enumeration; applied to the C-tensor value estimate invoked in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem mme_Ctensor_balanced_word_card (H m : ℕ) :
    Nat.card
        {w : Fin (H * m) → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m} =
      (H * m).factorial / ∏ _h : Fin H, m.factorial := by
  sorry
