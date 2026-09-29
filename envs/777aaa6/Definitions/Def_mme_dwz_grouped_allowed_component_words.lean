-- Prove2me | Definitions.Def_mme_dwz_grouped_allowed_component_words
-- name    : mme_dwz_grouped_allowed_component_words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:42:12.60134+00:00
-- url     : https://prove2.me/theorems/3f5bdbb5-b5ec-4967-9584-939f8787a63e
-- title:
--   Canonically grouped available Table-2 component words
-- statement:
--   Fix an integral scale $m\geq0$. The canonically grouped position set of the complete Table-2 standard tensor is
--
--   $$
--   P_m=\coprod_{s=0}^{14}\{0,\ldots,n_s m-1\},
--   $$
--
--   with outer label $s$ on the $s$th summand. For every component $s$, an available component word is a canonical $Z$-basis word of length $n_s m$ whose left fine grades have the exact prescribed Table-2 histogram. A grouped allowed family chooses such a word for every one of the fifteen rows. Reading a family at $(s,r)\in P_m$ produces the literal pair of left and right fine grades of its $r$th basis letter.
--
--   These are finite index definitions for the complete standard-form tensor. They introduce neither a tensor direct sum nor a retained/hole predicate, and they include $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4 and Definition 6.3, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_table2_useful_block

/-!
# Canonically grouped Table-2 component words

These definitions put the fifteen component powers in the same grouped order
as `dwzTable2StandardObj`.  They contain only finite index data; no tensor
direct sum or hole predicate is introduced.
-/

open MME

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- Positions in the fifteen component powers, grouped first by the literal
Table-2 row and then by the position inside that row's prescribed power. -/
abbrev GroupedPosition (m : ℕ) :=
  Σ s : Fin 15, Fin (MME.DWZTable2Counts.component s * m)

/-- The outer Table-2 component label of one canonically grouped position. -/
def groupedOuter {m : ℕ} (p : GroupedPosition m) : Fin 15 :=
  p.1

/-- One canonical component-power Z word satisfying the exact Table-2
availability histogram. -/
abbrev AvailableComponentWord (s : Fin 15) (m : ℕ) :=
  {w : PowIndex
      (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m) //
    componentWordAllowed s m w}

/-- A simultaneously available canonical Z word for every Table-2 row. -/
abbrev GroupedAllowedWords (m : ℕ) :=
  ∀ s : Fin 15, AvailableComponentWord.{u} s m

/-- The literal pair of fine left/right grades read at a grouped position. -/
def groupedFineZ {m : ℕ} (W : GroupedAllowedWords.{u} m)
    (p : GroupedPosition m) : Fin 3 × Fin 3 :=
  let letter := PowIndex.get
    (MME.DWZTable2Counts.component p.1 * m) (W p.1).1 p.2
  (letter.leftGrade, letter.rightGrade)

end MME.DWZComponentRestriction


