-- Prove2me | Definitions.Def_mme_dwz_positive_251_regional_profile_data
-- name    : mme_dwz_positive_251_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T02:21:32.714344+00:00
-- url     : https://prove2.me/theorems/9e77a711-61c0-4555-a0e7-977492c92be1
-- title:
--   Exact regional and original Z-profile data for the $T_{2,5,1}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{2,5,1}$ of $CW_5^{\otimes 4}$ (released object 161).
--
--   The Z-coordinate of $(2,5,1)$ is $k = 1$, so each coarse Z-block splits its index as $(k_1, 1-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ (the integers below); they sum to $1000000000000001$, so the exact normalized weights are those integers over $1000000000000001$.
--
--   The parent profile over $1000000000000001000000000000000$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 161, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent251

/-- Original object-161 parent profile of the canonical (2, 5, 1) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000001000000000000000
  denominator_pos := by norm_num
  count := ![499999999999055601905926078983, 500000000000945398094073921017, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999999999387, 500000000000613, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![499999999998644, 500000000001356, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![500000000000001, 499999999999999, 0, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-161 rotation weights rounded half-up to 10^15; they sum to 1000000000000001, so the
exact normalized weights are these integers over 1000000000000001. -/
def regionalWeight : Fin 3 → ℕ := ![553300007975230, 446699992024414, 357]

end MME.DWZPositiveComponent251


