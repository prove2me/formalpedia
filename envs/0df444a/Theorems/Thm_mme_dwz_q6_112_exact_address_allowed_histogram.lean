-- Prove2me | Theorems.Thm_mme_dwz_q6_112_exact_address_allowed_histogram
-- name    : mme_dwz_q6_112_exact_address_allowed_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:54:10.846598+00:00
-- url     : https://prove2.me/theorems/6ff11086-6579-44b0-be55-522477fab0fc
-- title:
--   The enhanced 112 hash profile equals the Table-2 allowed-word histogram
-- statement:
--   Specialize the enhanced q=6 coupled-constituent primary hash to the exact integral scale used by Table 2's 112 row. Every retained address then has length $c_{112}m$ and, after translating coupled Z grades to the canonical square's left fine grades, has the exact split histogram
--
--   $$
--   (422162412345m, 2008017975175310m, 422162412345m).
--   $$
--
--   The source-coordinate translation sends $(0,1,2)$ to $(2,0,1)$. This is the finite exact-profile landing condition required for the primary-hash extraction to factor through the literal restricted 112 component rather than the unrestricted canonical block power.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6(d), Section 6.3, and Table 2; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_q6_112_exact_profile_data

open MME

set_option autoImplicit false

theorem mme_dwz_q6_112_exact_address_allowed_histogram
    (m : ℕ)
    (address : CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m))) :
    (2 * (50000000 * (20088623 * m)) =
      MME.DWZTable2Counts.component (12 : Fin 15) * m) ∧
    ∀ a : Fin 3,
      Fintype.card
          {r : Fin (2 * (50000000 * (20088623 * m))) //
            mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = a} =
        MME.DWZTable2Counts.split (12 : Fin 15) a * m := by
  sorry
