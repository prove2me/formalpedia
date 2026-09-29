-- Prove2me | solution 1 for mme_dwz_grouped_allowed_words_useful_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:49:54.677969+00:00
-- url     : https://prove2.me/submissions/fc8b8854-461e-4bbe-ba1e-241cca825716

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_component_word_pointwise_coarse

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (W : GroupedAllowedWords.{u} m) :
    (∀ p : GroupedPosition m,
      MME.DWZTable2Counts.coarseOf (groupedFineZ W p) =
        MME.DWZSquare.shapeZ (groupedOuter p)) ∧
    ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card
          {p : GroupedPosition m //
            groupedOuter p = s ∧ (groupedFineZ W p).1 = a} =
        MME.DWZTable2Counts.split s a * m := by
  constructor
  · rintro ⟨s, r⟩
    exact mme_dwz_component_word_pointwise_coarse s m (W s).1 r
  · intro s a
    let e :
        {p : GroupedPosition m //
          groupedOuter p = s ∧ (groupedFineZ W p).1 = a} ≃
        {r : Fin (MME.DWZTable2Counts.component s * m) //
          (PowIndex.get _ (W s).1 r).leftGrade = a} :=
      {
      toFun p := by
        rcases p with ⟨⟨s', r⟩, hs, ha⟩
        dsimp only [groupedOuter] at hs
        subst s'
        exact ⟨r, ha⟩
      invFun r := ⟨⟨s, r.1⟩, rfl, r.2⟩
      left_inv p := by
        rcases p with ⟨⟨s', r⟩, hs, ha⟩
        dsimp only [groupedOuter] at hs
        subst s'
        rfl
      right_inv r := by
        rcases r with ⟨r, hr⟩
        rfl
      }
    calc
      Fintype.card
          {p : GroupedPosition m //
            groupedOuter p = s ∧ (groupedFineZ W p).1 = a} =
          Fintype.card
            {r : Fin (MME.DWZTable2Counts.component s * m) //
              (PowIndex.get _ (W s).1 r).leftGrade = a} :=
        Fintype.card_congr e
      _ = MME.DWZTable2Counts.split s a * m := (W s).2 a
