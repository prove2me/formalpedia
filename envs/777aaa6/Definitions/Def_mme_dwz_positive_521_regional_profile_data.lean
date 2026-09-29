-- Prove2me | Definitions.Def_mme_dwz_positive_521_regional_profile_data
-- name    : mme_dwz_positive_521_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-19T21:54:18.338502+00:00
-- url     : https://prove2.me/theorems/b944f634-da84-47ec-99cf-24c174dbfc32
-- title:
--   Exact regional and original Z-profile data for the $T_{5,2,1}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{5,2,1}$ of $CW_5^{\otimes 4}$ (released object 176).
--
--   The Z-coordinate of $(5,2,1)$ is $k = 1$, so each coarse Z-block splits its index as $(k_1, 1-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 176, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent521

/-- Original object-176 parent profile of the canonical (5, 2, 1) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![499999999999961090144755396854, 500000000000038909855244603146, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999999999899, 500000000000101, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999996733405, 500000003266595, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![500000000000038, 499999999999962, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-176 rotation weights, normalized over 10^15. -/
def regionalWeight : Fin 3 → ℕ := ![553308309396683, 73, 446691690603244]

end MME.DWZPositiveComponent521


