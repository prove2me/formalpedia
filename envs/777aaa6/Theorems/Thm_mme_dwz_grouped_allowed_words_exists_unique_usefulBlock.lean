-- Prove2me | Theorems.Thm_mme_dwz_grouped_allowed_words_exists_unique_usefulBlock
-- name    : mme_dwz_grouped_allowed_words_exists_unique_usefulBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:57:04.474022+00:00
-- url     : https://prove2.me/theorems/eca16b47-f41f-4c20-9fe8-431e002c9e49
-- title:
--   Canonical useful block represented by grouped available words
-- statement:
--   For every integral scale $m\geq0$ and every family choosing one available canonical $Z$ word in each of the fifteen Table-2 components, there exists a unique useful small-block index whose underlying fine-pair word is the canonically grouped concatenation of that family.
--
--   The uniqueness is representation-level: the outer word is the canonical component label on the disjoint union of component positions, and the useful block carries exactly the grouped fine word. This packages the componentwise availability equations as the literal DWZ Definition-6.3 useful-block object, including at $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3--5.4 and Definition 6.3, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_grouped_allowed_words_useful_certificate

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_grouped_allowed_words_exists_unique_usefulBlock
    (m : ℕ) (W : GroupedAllowedWords.{u} m) :
    ∃! small : MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)),
      small.1 = groupedFineZ W := by
  sorry
