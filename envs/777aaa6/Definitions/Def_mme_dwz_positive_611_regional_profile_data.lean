-- Prove2me | Definitions.Def_mme_dwz_positive_611_regional_profile_data
-- name    : mme_dwz_positive_611_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-19T16:51:39.141764+00:00
-- url     : https://prove2.me/theorems/9a8a5372-d217-4224-8b59-66b64d3eb629
-- title:
--   Exact regional and original Z-profile data for the {6,1,1}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{6,1,1}$ of $CW_5^{\otimes 4}$ (released object 179).
--
--   The Z-coordinate of $(6,1,1)$ is $k = 1$, so each coarse Z-block splits its index as $(k_1, 1-k_1)$ with $k_1 \in \{0,1\}$, and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$, and **region 2 has weight exactly zero** in the released data.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture of the regional profiles:
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   so the parent frequencies are approximately $(0.4999998,\ 0.5000002)$ on $k_1 = 0, 1$. This is the original profile of the released object, not a canonicalized child profile; the equality above is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 179, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data (consumer 40).

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent611

/-- Original object-179 parent profile of the canonical (6,1,1) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![499999805123810866169579372640, 500000194876189133830420627360, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999707742502, 500000292257498, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999999883158, 500000000116842, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999996102302, 500000003897698, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Region 2 carries rotation weight exactly zero in the released object-179 data. -/
def regionalWeight : Fin 3 → ℕ := ![666662934904310, 333337065095690, 0]

end MME.DWZPositiveComponent611


