-- Prove2me | Definitions.Def_mme_dwz_positive_323_regional_profile_data
-- name    : mme_dwz_positive_323_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T02:46:01.966983+00:00
-- url     : https://prove2.me/theorems/d7dae6b1-427e-4e21-85ce-123dcf908e01
-- title:
--   Exact regional and original Z-profile data for the $T_{3,2,3}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{3,2,3}$ of $CW_5^{\otimes 4}$ (released object 165).
--
--   The Z-coordinate of $(3,2,3)$ is $k = 3$, so each coarse Z-block splits its index as $(k_1, 3-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ and exactly normalized; they sum to $10^{15}$.
--
--   The parent profile over $10^{30}$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 165, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent323

/-- Original object-165 parent profile of the canonical (3, 2, 3) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000000000000000000000
  denominator_pos := by norm_num
  count := ![13132303930840513093638902826, 486867529943998775058158721588, 486867886232516212456172802005, 13132279892644499392029573581, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![211757704766299, 288349900668285, 289129887774821, 210762506790595, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![13110601585652, 486889231720008, 486889590231189, 13110576463151, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![13215752642433, 486784083414081, 486784431102284, 13215732841202, 0]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-165 rotation weights, normalized over 10^15. -/
def regionalWeight : Fin 3 → ℕ := ![13890405, 793634148579384, 206365837530211]

end MME.DWZPositiveComponent323


