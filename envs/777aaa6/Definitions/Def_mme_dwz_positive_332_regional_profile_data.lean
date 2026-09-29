-- Prove2me | Definitions.Def_mme_dwz_positive_332_regional_profile_data
-- name    : mme_dwz_positive_332_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T02:49:11.80449+00:00
-- url     : https://prove2.me/theorems/0465d69d-cd97-41a6-8741-e9f8319eb048
-- title:
--   Exact regional and original Z-profile data for the $T_{3,3,2}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{3,3,2}$ of $CW_5^{\otimes 4}$ (released object 166).
--
--   The Z-coordinate of $(3,3,2)$ is $k = 2$, so each coarse Z-block splits its index as $(k_1, 2-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 166, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent332

/-- Original object-166 parent profile of the canonical (3, 3, 2) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![182244070954619267895565448840, 635511971102645667357472221678, 182243957942735064746962329482, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![180456651105690, 639086873058872, 180456475835438, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![182709459568767, 634581177664126, 182709362767107, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![299995520037815, 400008991933341, 299995488028844, 0, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-166 rotation weights, normalized over 10^15. -/
def regionalWeight : Fin 3 → ℕ := ![206582338214088, 793417646219670, 15566242]

end MME.DWZPositiveComponent332


