-- Prove2me | Definitions.Def_mme_dwz_fourth_literal202_row_data
-- name    : mme_dwz_fourth_literal202_row_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T08:33:01.098839+00:00
-- url     : https://prove2.me/theorems/956f782d-631f-4bac-83a0-4d27e53cd58e
-- title:
--   Exact rational profiles for the nineteen fourth-power 202 component records
-- statement:
--   Let $p_i=(c_{i,0},c_{i,1},c_{i,2})/d_i$ be each of the nineteen literal $(2,0,2)$ component profiles in the $q=5$ fourth-power certificate. Each record stores its original ledger index and object identifier, a positive denominator $d_i$, nonnegative integer counts summing to $d_i$, and an exact rational logarithmic rate $r_i$. These are the actual 202 records, not copies of the differing 022 profiles. The profile constructor is formally checked; the definition itself makes no tensor-value claim.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Section 8.3 and Table 3; exact rational decode of the local q=5 fourth-power certificate used for the existing fixed-tau mission. Ledger indices and object identifiers are formalization bookkeeping, not paper numbering.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic

open BigOperators MME.DWZRestrictedValue
set_option autoImplicit false

namespace MME.ZEndpoint202PublicRows

structure Row where
  ledgerIndex : ℕ
  objectId : ℕ
  denominator : ℕ
  counts : Fin 3 → ℕ
  rate : ℚ

def rows : Fin 19 → Row := ![
  { ledgerIndex := 15, objectId := 16, denominator := 1000000000000001, counts := ![37034147523554, 925931705102510, 37034147373937], rate := (2605830108083 / 1000000000000 : Rat) },
  { ledgerIndex := 35, objectId := 24, denominator := 250000000000000, counts := ![9300034303238, 231399931410383, 9300034286379], rate := (2605829497491 / 1000000000000 : Rat) },
  { ledgerIndex := 42, objectId := 27, denominator := 1000000000000000, counts := ![38923052937811, 922153894160729, 38923052901460], rate := (2605749367259 / 1000000000000 : Rat) },
  { ledgerIndex := 49, objectId := 30, denominator := 999999999999999, counts := ![48188160693555, 903623678219867, 48188161086577], rate := (130159698449 / 50000000000 : Rat) },
  { ledgerIndex := 56, objectId := 33, denominator := 1000000000000000, counts := ![404661808449122, 190676382719271, 404661808831607], rate := (164250766959 / 125000000000 : Rat) },
  { ledgerIndex := 69, objectId := 36, denominator := 1000000000000000, counts := ![403454714759561, 193090573085681, 403454712154758], rate := (1321571617993 / 1000000000000 : Rat) },
  { ledgerIndex := 76, objectId := 39, denominator := 500000000000000, counts := ![27603813274839, 444792385226705, 27603801498456], rate := (2599143481523 / 1000000000000 : Rat) },
  { ledgerIndex := 83, objectId := 42, denominator := 1000000000000000, counts := ![57051511088545, 885896840599424, 57051648312031], rate := (40590758841 / 15625000000 : Rat) },
  { ledgerIndex := 90, objectId := 45, denominator := 1000000000000001, counts := ![43587809900576, 912824379832484, 43587810266941], rate := (2604890148383 / 1000000000000 : Rat) },
  { ledgerIndex := 97, objectId := 48, denominator := 1000000000000000, counts := ![37628947587229, 924742103982061, 37628948430710], rate := (2605822076001 / 1000000000000 : Rat) },
  { ledgerIndex := 106, objectId := 51, denominator := 1000000000000000, counts := ![48173101127298, 903653799320607, 48173099552095], rate := (650800203351 / 250000000000 : Rat) },
  { ledgerIndex := 113, objectId := 54, denominator := 1000000000000000, counts := ![57152352354681, 885695321145251, 57152326500068], rate := (324716566107 / 125000000000 : Rat) },
  { ledgerIndex := 120, objectId := 57, denominator := 1000000000000000, counts := ![52899054671426, 894201970007713, 52898975320861], rate := (325082501183 / 125000000000 : Rat) },
  { ledgerIndex := 127, objectId := 60, denominator := 1000000000000000, counts := ![39309181482517, 921381637035301, 39309181482182], rate := (130285663883 / 50000000000 : Rat) },
  { ledgerIndex := 136, objectId := 63, denominator := 500000000000000, counts := ![19656752067590, 460686495865381, 19656752067029], rate := (162857052293 / 62500000000 : Rat) },
  { ledgerIndex := 143, objectId := 66, denominator := 999999999999999, counts := ![43583834711735, 912832330529485, 43583834758779], rate := (2604891261379 / 1000000000000 : Rat) },
  { ledgerIndex := 150, objectId := 69, denominator := 200000000000000, counts := ![9637765145873, 180724461156025, 9637773698102], rate := (650798414231 / 250000000000 : Rat) },
  { ledgerIndex := 159, objectId := 72, denominator := 500000000000000, counts := ![18813898207999, 462372203554262, 18813898237739], rate := (65145552679 / 25000000000 : Rat) },
  { ledgerIndex := 166, objectId := 75, denominator := 1000000000000000, counts := ![333333333177518, 333333333644965, 333333333177517], rate := (343387464803 / 200000000000 : Rat) }]

def profile (i : Fin 19) : IntegerZSplitProfile 3 where
  denominator := (rows i).denominator
  denominator_pos := by decide +kernel +revert
  count := (rows i).counts
  count_sum := by decide +kernel +revert

def frequency (i : Fin 19) (a : Fin 3) : ℚ :=
  ((rows i).counts a : ℚ) / (rows i).denominator

end MME.ZEndpoint202PublicRows


