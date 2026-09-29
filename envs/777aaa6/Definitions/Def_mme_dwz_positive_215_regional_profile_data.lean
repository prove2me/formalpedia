-- Prove2me | Definitions.Def_mme_dwz_positive_215_regional_profile_data
-- name    : mme_dwz_positive_215_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-19T21:18:19.218669+00:00
-- url     : https://prove2.me/theorems/b9343630-efc1-4392-9d75-d78cf5f1f005
-- title:
--   Exact regional and original Z-profile data for the $T_{2,1,5}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{2,1,5}$ of $CW_5^{\otimes 4}$ (released object 157).
--
--   The Z-coordinate of $((2,1,5))$ is $k = 5$, so each coarse Z-block splits its index as $(k_1, 5-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 157, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent215

/-- Original object-157 parent profile of the canonical (2, 1, 5) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![0, 1391630958173011920935089105, 498608739167650629785623212965, 498607981201181818955886747224, 1391648672994539337554950706]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 195444603237026, 304448626510453, 304588584996941, 195518185255580]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 1362859596272, 498637505251293, 498636758180581, 1362876971854]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 1414940026837, 498585434397678, 498584667570237, 1414958005248]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-157 rotation weights, normalized over 10^15. -/
def regionalWeight : Fin 3 → ℕ := ![87104180, 447883575570391, 552116337325429]

end MME.DWZPositiveComponent215


