-- Prove2me | Definitions.Def_Kourovka_Presentations_RelatorCodes
-- name    : Kourovka_Presentations_RelatorCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:53.764344+00:00
-- url     : https://prove2.me/theorems/001d4a87-1c00-47d5-bdef-927785271cae
-- title:
--   Relator Codes
-- statement:
--   Definitions and structural lemmas for Relator Codes, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/RelatorCodes.lean

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
attribute [refl] MulEquiv.refl
namespace Kourovka.MetabelianEnumeration.WordCertificates
def encodeWord {n : ℕ} (w : Word n) : List (ℕ × Bool) :=
  w.map fun letter => (letter.1.val, letter.2)
theorem interpret_encodeWord {n : ℕ} (w : Word n) :
    interpretWord n (encodeWord w) = FreeGroup.mk w := by
  rw [← FreeGroup.lift_of_apply (FreeGroup.mk w), FreeGroup.lift_mk]
  simp only [interpretWord, encodeWord, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;> simp [i.isLt]
def encodeRelators {n : ℕ} (rels : List (FreeGroup (Fin n))) : PresentationCode :=
  (n, rels.map fun r => encodeWord r.toWord)
theorem relations_encodeRelators {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    relations (encodeRelators rels) = relSet rels := by
  ext r
  simp [relations, encodeRelators, List.map_map, relSet, Function.comp_def,
    interpret_encodeWord, FreeGroup.mk_toWord]
  rfl
def codeGroupEquiv {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Kourovka.MetabelianEnumeration.GroupOf (encodeRelators rels) ≃*
      PresentedGroup (relSet rels) := by
  change PresentedGroup (relations (encodeRelators rels)) ≃* PresentedGroup (relSet rels)
  rw [relations_encodeRelators]
  exact MulEquiv.refl _
end Kourovka.MetabelianEnumeration.WordCertificates


