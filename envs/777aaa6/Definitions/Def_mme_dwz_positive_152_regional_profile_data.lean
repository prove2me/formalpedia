-- Prove2me | Definitions.Def_mme_dwz_positive_152_regional_profile_data
-- name    : mme_dwz_positive_152_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T02:03:50.628985+00:00
-- url     : https://prove2.me/theorems/c9924503-1d80-468b-897d-76cca7b86112
-- title:
--   Exact regional and original Z-profile data for the $T_{1,5,2}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{1,5,2}$ of $CW_5^{\otimes 4}$ (released object 153).
--
--   The Z-coordinate of $(1,5,2)$ is $k = 2$, so each coarse Z-block splits its index as $(k_1, 2-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ (the integers below); they sum to $999999999999999$, so the exact normalized weights are those integers over $999999999999999$.
--
--   The parent profile over $999999999999999000000000000000$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 153, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent152

/-- Original object-153 parent profile of the canonical (1, 5, 2) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 999999999999999000000000000000
  denominator_pos := by norm_num
  count := ![182525590368009350337674025336, 634946649617848200586791611772, 182527760014141449075534362892, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![182609266133889, 634779342980541, 182611390885570, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![182457991461446, 635081811128591, 182460197409963, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![326659447055176, 346917575209532, 326422977735292, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-153 rotation weights rounded half-up to 10^15; they sum to 999999999999999, so the
exact normalized weights are these integers over 999999999999999. -/
def regionalWeight : Fin 3 → ℕ := ![446752073791344, 553247810863512, 115345143]

end MME.DWZPositiveComponent152


