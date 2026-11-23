-- Prove2me | Theorems.Thm_mem_ConcatInf_IterOmega
-- name    : mem_ConcatInf_IterOmega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:21.423341+00:00
-- url     : https://prove2.me/theorems/5fcd514e-c505-4c89-84c2-9c15b3a9fe3c
-- title:
--   mem Concat Inf Iter Omega: mem Concat Inf Iter Omega
-- statement:
--   The mem Concat Inf Iter Omega construction uses the mem Concat Inf Iter Omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L213-L224
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L213-L224

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem mem_ConcatInf_IterOmega {L0 L1 : Set (List A)} {as : Stream' A}
    (h : as ∈ L0 * L1^ω) : ∃ φ : Stream' ℕ, StrictMono φ ∧
      as.extract 0 (φ 0) ∈ L0 ∧ ∀ m, as.extract (φ m) (φ (m + 1)) ∈ L1 := by sorry
