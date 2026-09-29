-- Prove2me | Definitions.Def_mme_dwz_fourth_literal022_row_data
-- name    : mme_dwz_fourth_literal022_row_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T08:08:59.566586+00:00
-- url     : https://prove2.me/theorems/e9317245-9f63-46a1-aa48-e0b655c1df3b
-- title:
--   Exact rational profiles for the nineteen fourth-power 022 component records
-- statement:
--   This records the nineteen literal 022 component profiles in the q=5 fourth-power numerical certificate. Each row stores its original ledger index and object identifier, a positive denominator D, nonnegative integer counts (c0,c1,c2) summing to D, and an exact rational logarithmic rate. The constructor gives the corresponding normalized prescribed-Z profile. These are fixed data from the current local fourth-power certificate; they do not assert any tensor-value conclusion.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Section 8.3 and Table 3; exact rational decode of the local q=5 fourth-power certificate used for the existing fixed-tau mission. Ledger indices and object identifiers are formalization bookkeeping, not paper numbering.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic

open BigOperators MME.DWZRestrictedValue
set_option autoImplicit false

namespace MME.ZEndpoint022PublicRows

structure Row where
  ledgerIndex : ℕ
  objectId : ℕ
  denominator : ℕ
  counts : Fin 3 → ℕ
  rate : ℚ

def rows : Fin 19 → Row := ![
  { ledgerIndex := 14, objectId := 9, denominator := 1000000000000000, counts := ![37033909639967, 925932180476533, 37033909883500], rate := (2605830108047 / 1000000000000 : Rat) },
  { ledgerIndex := 32, objectId := 22, denominator := 1000000000000001, counts := ![403380669960589, 193238676801698, 403380653237714], rate := (264406954617 / 200000000000 : Rat) },
  { ledgerIndex := 39, objectId := 25, denominator := 1000000000000001, counts := ![48173663469861, 903652672867995, 48173663662145], rate := (650800139397 / 250000000000 : Rat) },
  { ledgerIndex := 46, objectId := 28, denominator := 1000000000000000, counts := ![39313745523889, 921372508914297, 39313745561814], rate := (2605712812037 / 1000000000000 : Rat) },
  { ledgerIndex := 53, objectId := 31, denominator := 1000000000000000, counts := ![37627285994512, 924745428003365, 37627286002123], rate := (2605822120953 / 1000000000000 : Rat) },
  { ledgerIndex := 66, objectId := 34, denominator := 1000000000000000, counts := ![37200136513905, 925599726985811, 37200136500284], rate := (2605829497497 / 1000000000000 : Rat) },
  { ledgerIndex := 73, objectId := 37, denominator := 1000000000000000, counts := ![43205437446463, 913589124530632, 43205438022905], rate := (1302497159987 / 500000000000 : Rat) },
  { ledgerIndex := 80, objectId := 40, denominator := 1000000000000000, counts := ![52872504103269, 894255111759066, 52872384137665], rate := (26006764397 / 10000000000 : Rat) },
  { ledgerIndex := 87, objectId := 43, denominator := 1000000000000000, counts := ![55265633936126, 889468731626683, 55265634437191], rate := (1299551565421 / 500000000000 : Rat) },
  { ledgerIndex := 94, objectId := 46, denominator := 333333333333333, counts := ![111111111053069, 111111111227195, 111111111053069], rate := (429234331027 / 250000000000 : Rat) },
  { ledgerIndex := 103, objectId := 49, denominator := 1000000000000001, counts := ![38922930458559, 922154139210089, 38922930331353], rate := (325718672209 / 125000000000 : Rat) },
  { ledgerIndex := 110, objectId := 52, denominator := 999999999999999, counts := ![52893037829213, 894214128137930, 52892834032856], rate := (2600663770567 / 1000000000000 : Rat) },
  { ledgerIndex := 117, objectId := 55, denominator := 500000000000000, counts := ![28537703935299, 442924576329475, 28537719735226], rate := (324723825121 / 125000000000 : Rat) },
  { ledgerIndex := 124, objectId := 58, denominator := 1000000000000000, counts := ![48188699360936, 903622601140799, 48188699498265], rate := (1301596862041 / 500000000000 : Rat) },
  { ledgerIndex := 133, objectId := 61, denominator := 1000000000000000, counts := ![48188147199271, 903623705460121, 48188147340608], rate := (1301596987587 / 500000000000 : Rat) },
  { ledgerIndex := 140, objectId := 64, denominator := 1000000000000000, counts := ![55269512449195, 889460974713096, 55269512837709], rate := (519820085927 / 200000000000 : Rat) },
  { ledgerIndex := 147, objectId := 67, denominator := 1000000000000000, counts := ![39309211984339, 921381570625483, 39309217390178], rate := (651428318569 / 250000000000 : Rat) },
  { ledgerIndex := 156, objectId := 70, denominator := 1000000000000000, counts := ![405428415388205, 189143166661914, 405428417949881], rate := (1309185925269 / 1000000000000 : Rat) },
  { ledgerIndex := 163, objectId := 73, denominator := 1000000000000000, counts := ![37630089893749, 924739822340272, 37630087765979], rate := (2605822045073 / 1000000000000 : Rat) }]

def profile (i : Fin 19) : IntegerZSplitProfile 3 where
  denominator := (rows i).denominator
  denominator_pos := by decide +kernel +revert
  count := (rows i).counts
  count_sum := by decide +kernel +revert

def frequency (i : Fin 19) (a : Fin 3) : ℚ :=
  ((rows i).counts a : ℚ) / (rows i).denominator

end MME.ZEndpoint022PublicRows


