-- Prove2me | solution 1 for mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:49:56.370702+00:00
-- url     : https://prove2.me/submissions/7b6e895e-e730-4f22-b4ed-8dc86d16e074

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME

universe u v

set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

/-- A surviving canonical Z word in the correlated common-state broken copy
annihilates any value whose nonvanishing would make a distinct owner
compatible with that same word.  This is the exact `Keeps` interface needed
for the remaining mixed-Z singleton tensor. -/
theorem solution
    {V : Type v} [Zero V]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (owner competitor : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : V)
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge owner)
      (commonStateBrokenCopy m reindex q edge owner) W)
    (hne : competitor ≠ owner)
    (hCompatible : x ≠ 0 →
      ∀ hUseful : addressWordUseful m
          (sourceWord reindex edge owner) W,
        ownerCompatible m reindex q edge owner
          (addressUsefulBlock m (sourceWord reindex edge owner) W hUseful)
          competitor) :
    x = 0 := by
  classical
  by_contra hx
  obtain ⟨hUseful, hNonhole⟩ := hSurvives
  have hKeeps :
      ∀ j', ownerCompatible m reindex q edge owner
          (addressUsefulBlock m (sourceWord reindex edge owner) W hUseful) j' →
        j' = owner := by
    have hAll := hNonhole
    simp only [commonStateBrokenCopy, MME.DWZStep2.brokenCopy,
      Finset.mem_filter, Finset.mem_univ, true_and,
      MME.DWZStep2.Keeps] at hAll
    exact hAll.2
  exact hne (hKeeps competitor (hCompatible hx hUseful))
