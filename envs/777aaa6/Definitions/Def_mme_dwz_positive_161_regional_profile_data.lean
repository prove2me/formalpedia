-- Prove2me | Definitions.Def_mme_dwz_positive_161_regional_profile_data
-- name    : mme_dwz_positive_161_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-19T16:31:29.888968+00:00
-- url     : https://prove2.me/theorems/17e9f4a5-e537-4b24-84a8-be45de56ea10
-- title:
--   Exact regional and original Z-profile data for the {1,6,1}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{1,6,1}$ of $CW_5^{\otimes 4}$ (released object 154).
--
--   The Z-coordinate of $(1,6,1)$ is $k = 1$, so each coarse Z-block splits its index as $(k_1, 1-k_1)$ with $k_1 \in \{0,1\}$, and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$, and **region 1 has weight exactly zero** in the released data.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture of the regional profiles:
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   so the parent frequencies are approximately $(0.4999998,\ 0.5000002)$ on $k_1 = 0, 1$. This is the original profile of the released object, not a canonicalized child profile; the equality above is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1 (regional split). Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 154, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data (consumer 15).

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent161

/-- Original object-154 parent profile of the canonical (1,6,1) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![499999836852560862758332349976, 500000163147439137241667650024, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999755343243, 500000244656757, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![500000004248565, 499999995751435, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999999868661, 500000000131339, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Region 1 carries rotation weight exactly zero in the released object-154 data. -/
def regionalWeight : Fin 3 → ℕ := ![666663210191268, 0, 333336789808732]

end MME.DWZPositiveComponent161


