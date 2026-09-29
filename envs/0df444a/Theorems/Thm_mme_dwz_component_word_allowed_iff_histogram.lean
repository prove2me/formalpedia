-- Prove2me | Theorems.Thm_mme_dwz_component_word_allowed_iff_histogram
-- name    : mme_dwz_component_word_allowed_iff_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:07:59.912308+00:00
-- url     : https://prove2.me/theorems/424afd7b-e18a-4730-acba-38e623e25346
-- title:
--   Available component words are exactly the Table-2 split histogram
-- statement:
--   Fix a Table-2 component $s$, a scale $m\geq0$, and a canonical $Z$-basis word $w$ of length $n_sm$. Then $w$ is available for the restricted component if and only if, for every left split grade $a\in\{0,1,2\}$,
--
--   $$
--   \#\{r\in[n_sm]:\operatorname{leftGrade}(w_r)=a\}=n_{s,a}m,
--   $$
--
--   where $n_s$ and $n_{s,a}$ are the exact integer component and split counts transcribed from Table 2.
--
--   This identifies the formal allowed-word predicate with Definition 5.4 availability component by component. It includes $m=0$, where the unique empty word has three zero cell counts.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4, PDF p. 48 / printed p. 47, specialized to Section 6.3 Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_component_word_allowed_iff_histogram
    (s : Fin 15) (m : ℕ)
    (w : MME.DWZComponentRestriction.PowIndex
      (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) :
    MME.DWZComponentRestriction.componentWordAllowed s m w ↔
      ∀ a : Fin 3,
        Fintype.card
            {r : Fin (MME.DWZTable2Counts.component s * m) //
              (MME.DWZComponentRestriction.PowIndex.get _ w r).leftGrade = a} =
          MME.DWZTable2Counts.split s a * m := by
  sorry
