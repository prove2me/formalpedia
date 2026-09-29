-- Prove2me | Definitions.Def_mme_dwz_fourth_elementary_four_row_data
-- name    : mme_dwz_fourth_elementary_four_row_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T09:17:29.603128+00:00
-- url     : https://prove2.me/theorems/cae44513-41d7-4f06-af74-5648c9f175a2
-- title:
--   Exact original profiles for four elementary q=5 square-component rows
-- statement:
--   This table records the four residual elementary CW-square profiles in the local q=5 fourth-power certificate: ledger indices 10,12,18,19 with literal addresses 013,301,031,103. Each row stores its original object identifier, coarse address, denominator, and three integer Z counts. The counts are copied exactly from the existing ledger; no symmetrization or profile replacement is performed. Their common candidate logarithmic rate is 1820522261843/1000000000000 at tau=790643/1000000. The corresponding integral prescribed-Z profiles are normalized by construction. These data do not themselves assert a tensor-value lower bound.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Definitions 3.7 and 3.9; exact rational row extraction from the local q=5 fourth-power numerical certificate. Ledger indices and object identifiers are formalization bookkeeping, not paper numbering.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
open BigOperators MME.DWZRestrictedValue

namespace MME.ElementaryFourScalar

structure Row where
  ledgerIndex : ℕ
  objectId : ℕ
  address : Fin 3 → ℕ
  denominator : ℕ
  counts : Fin 3 → ℕ

def rows : Fin 4 → Row := ![
  { ledgerIndex := 10, objectId := 8, address := ![0,1,3],
    denominator := 500000000000000, counts := ![0,249999999930157,250000000069843] },
  { ledgerIndex := 12, objectId := 19, address := ![3,0,1],
    denominator := 1000000000000000, counts := ![499999999026019,500000000973981,0] },
  { ledgerIndex := 18, objectId := 10, address := ![0,3,1],
    denominator := 500000000000000, counts := ![249999999930157,250000000069843,0] },
  { ledgerIndex := 19, objectId := 12, address := ![1,0,3],
    denominator := 1000000000000000, counts := ![0,499999999026019,500000000973981] }]

def profile (i : Fin 4) : IntegerZSplitProfile 3 where
  denominator := (rows i).denominator
  denominator_pos := by decide +kernel +revert
  count := (rows i).counts
  count_sum := by decide +kernel +revert

def frequency (i : Fin 4) (a : Fin 3) : ℚ :=
  ((rows i).counts a : ℚ) / (rows i).denominator

def tau : ℚ := 790643 / 1000000
def rate : ℚ := 1820522261843 / 1000000000000


end MME.ElementaryFourScalar


