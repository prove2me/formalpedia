-- Prove2me | Definitions.Def_mme_dwz_positive_116_regional_profile_data
-- name    : mme_dwz_positive_116_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-17T10:10:25.698199+00:00
-- url     : https://prove2.me/theorems/d1706882-e68d-4d51-b8ef-5e9c1ad25499
-- title:
--   Original positive CW116 profile and its three exact regional profiles
-- statement:
--   This fixes the exact original prescribed-Z profile of the fourth-level CW component $T_{1,1,6}$ (object 149 in the supplied q=5 certificate) and its three regional parent profiles.
--
--   The parent denominator is $10^{30}$, with grade-$0,1,2,3,4$ count vector
--   $$
--   (0,0,15632850634043171218716057,
--   999968734317748997496639110491,
--   15632831616959332142173452).
--   $$
--   Each regional denominator is $10^{15}$. The corresponding count vectors are
--   $$
--   \begin{aligned}
--   p^{(0)}&=(0,0,3672979602,999992653387403,3673632995),\\
--   p^{(1)}&=(0,0,21608863616,999956782309566,21608826818),\\
--   p^{(2)}&=(0,0,21609500019,999956781673203,21608826778).
--   \end{aligned}
--   $$
--   The integer regional weight numerators are
--   $$
--   (A_0,A_1,A_2)=(333199364706116,333400336186257,333400299107627),
--   $$
--   with common denominator $10^{15}$. Thus at parent multiplicity $m$, region $r$ is intended to have multiplicity $A_rm$.
--
--   This is pure exact data with normalized integer-profile constructor proofs. The weighted-mixture identity and the induced tensor restriction are separate theorem obligations. These are regional profiles of the fourth-level parent, not the canonicalized fine profiles of its square children; no entropy or component-value certificate is included.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7 Claim 7.1, https://arxiv.org/html/2210.10173v5#S7. Concrete data: supplied certificates/mme_dwz_power4_tau_790643_1000000.json, recursive_child_graph.nodes object 149; exact source rationalization from scripts/build_exact_scalar_bound.py (round-half-up to 10^15 then normalize); original parent counts from Solutions/Sol_mme_dwz_fourth_tensor_ledger_metadata.lean, objectId149/address116; region profiles are the coarse-Z marginals of public mme_dwz_fourth_rational_recursive_entropy_data witnesses0,1,2 (10b34313-45be-4f95-bc19-c4301ee0b2ce).

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent116

/-- Original object-149 parent profile, not a canonicalized child profile. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![0, 0, 15632850634043171218716057,
    999968734317748997496639110491, 15632831616959332142173452]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 0, 3672979602, 999992653387403, 3673632995]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 0, 21608863616, 999956782309566, 21608826818]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 0, 21609500019, 999956781673203, 21608826778]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

def regionalWeight : Fin 3 → ℕ := ![333199364706116, 333400336186257, 333400299107627]

end MME.DWZPositiveComponent116


