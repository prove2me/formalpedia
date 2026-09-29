-- Prove2me | Definitions.Def_mme_dwz_retained_fine_address
-- name    : mme_dwz_retained_fine_address
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:17:27.74484+00:00
-- url     : https://prove2.me/theorems/c653f6c8-0859-481e-ae2d-946387252600
-- title:
--   Canonical fine address of a retained DWZ block
-- statement:
--   For each retained large block, tensor mode, and power position, suppose the two copies of the Coppersmith--Winograd tensor carry grades in $\{0,1,2\}$. Their ordered pair defines a label in the canonical nine-grading of $CW_q\otimes CW_q$. The resulting function is the literal refined address used when testing support after the additional zeroing steps.
--
--   Unlike a dimension or cardinality encoding, this definition retains both grade coordinates at every tensor-power position, so its block-support predicate is the actual canonical fine-grading projection.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1, Additional Zeroing-Out Steps 1--2 and Claim 6.2, printed pp. 51--53 (PDF pp. 52--54); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME.DWZStep1Support

namespace MME.DWZStep2Source

set_option autoImplicit false
set_option warningAsError true

/-- The literal fine-nine-grading address determined by the two canonical
`CW_q` grade words in every retained copy, mode, and tensor-power position. -/
def retainedFineAddress
    {Copy Position : Type*}
    (left right : Copy → Fin 3 → Position → Fin 3) :
    Copy → Fin 3 → Position → Fin (3 * 3) :=
  fun j i r ↦ fineSplitGrade (left j i r) (right j i r)

end MME.DWZStep2Source


