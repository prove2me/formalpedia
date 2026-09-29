-- Prove2me | Theorems.Thm_mme_dwz_grouped_allowed_words_useful_certificate
-- name    : mme_dwz_grouped_allowed_words_useful_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:48:08.253848+00:00
-- url     : https://prove2.me/theorems/61cd6c6d-e29f-4f83-98a7-34649d2f1be9
-- title:
--   Grouped available component words form a useful Table-2 fine block
-- statement:
--   Fix a scale $m\geq0$ and choose, for each of the fifteen Table-2 components $s$, one available canonical $Z$-basis word of length $n_s m$. Concatenate the words in canonical component order and label every position by the pair of fine left and right grades of its basis letter. Then every fine pair coarsens to the outer $Z$-degree of its component, and for every component $s$ and left fine grade $a$,
--
--   $$
--   \#\{p:\operatorname{outer}(p)=s,\ \operatorname{left}(p)=a\}=n_{s,a}m.
--   $$
--
--   Consequently this grouped fine word satisfies exactly the componentwise availability/usefulness conditions of DWZ Definitions 5.4 and 6.3. The result includes zero-length component words and does not aggregate interior rows into the regional Equation-(23) encoding.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3--5.4 and Definition 6.3, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_component_word_pointwise_coarse

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_grouped_allowed_words_useful_certificate
    (m : ℕ) (W : GroupedAllowedWords.{u} m) :
    (∀ p : GroupedPosition m,
      MME.DWZTable2Counts.coarseOf (groupedFineZ W p) =
        MME.DWZSquare.shapeZ (groupedOuter p)) ∧
    ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card
          {p : GroupedPosition m //
            groupedOuter p = s ∧ (groupedFineZ W p).1 = a} =
        MME.DWZTable2Counts.split s a * m := by
  sorry
