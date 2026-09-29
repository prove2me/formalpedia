-- Prove2me | Theorems.Thm_mme_dwz_sourceWord_exact_profile_transport
-- name    : mme_dwz_sourceWord_exact_profile_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:58:19.784809+00:00
-- url     : https://prove2.me/theorems/a21bcfaa-2c70-4a5f-9f8e-8cf7b6d95406
-- title:
--   Source-coordinate reindexing preserves the exact Table-2 profile
-- statement:
--   Let a finite family of fifteen-component words have the exact Table-2 component histogram at scale $m$. Reindex every coordinate through an equivalence $\operatorname{Fin}(N+1) \simeq \operatorname{Fin}(L)$. For every owner and every component label, the reindexed source word has exactly the same fiber cardinality, and therefore the same prescribed Table-2 profile. This transports the output of affine hashing to the coordinate order used by the literal CW tensor source.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, source-family reindexing in the proof of Theorem 6.1.

import Definitions.Def_mme_dwz_global_common_state_broken_copy

set_option autoImplicit false

theorem mme_dwz_sourceWord_exact_profile_transport
    (m : ℕ) {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hprofile : ∀ r s,
      Fintype.card {t : Fin (N + 1) // edge r t = s} =
        MME.DWZTable2Counts.component s * m) :
    ∀ r s,
      Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
        MME.DWZTable2Counts.component s * m := by
  sorry
