-- Prove2me | Definitions.Def_mme_dwz_positive_125_regional_profile_data
-- name    : mme_dwz_positive_125_regional_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T01:42:51.084981+00:00
-- url     : https://prove2.me/theorems/a32d2d5e-5432-4498-9915-82210295c653
-- title:
--   Exact regional and original Z-profile data for the $T_{1,2,5}$ component
-- statement:
--   Exact rational Z-split data for the positive fourth-level constituent $T_{1,2,5}$ of $CW_5^{\otimes 4}$ (released object 150).
--
--   The Z-coordinate of $(1,2,5)$ is $k = 5$, so each coarse Z-block splits its index as $(k_1, 5-k_1)$ and a profile records the frequencies of the left grade $k_1$. The three regional profiles are the coarse-Z marginals of the public recursive witnesses for this consumer, each over denominator $10^{15}$. The regional weights are the released rotation proportions rounded half-up to $10^{15}$ (the integers below); they sum to $1000000000000001$, so the exact normalized weights are those integers over $1000000000000001$.
--
--   The parent profile over $1000000000000001000000000000000$ is the exact weighted mixture
--
--   $$\text{count}_{\text{parent}}(a) \;=\; \sum_{r} \text{count}_r(a)\,\cdot\,W_r ,$$
--
--   which is the original profile of the released object, not a canonicalized child profile. The equality is checked by kernel arithmetic in the companion regional-restriction theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 (printed pp. 23-24) and Section 7, Claim 7.1. Released data power4_dup_2.371919.mat (SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb), object 150, rationalized by round-half-up to denominator 10^15 then exact normalization, with regional profiles the coarse-Z marginals of the public recursive witnesses in mme_dwz_fourth_rational_recursive_entropy_data.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open MME.DWZRestrictedValue BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZPositiveComponent125

/-- Original object-150 parent profile of the canonical (1, 2, 5) constituent, not a
canonicalized child profile. It is the exact regional mixture below. -/
def parentProfile : IntegerZSplitProfile 5 where
  denominator := 1000000000000001000000000000000
  denominator_pos := by norm_num
  count := ![0, 1391521776134589574137594393, 498608940440923927790391158037, 498607997716856279216764679186, 1391540066086203418706568384]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region0 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 195019571365019, 305306995049943, 304654823774872, 195018609810166]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region1 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 1414888128362, 498585576313964, 498584628842149, 1414906715525]
  count_sum := by norm_num [Fin.sum_univ_succ]

def region2 : IntegerZSplitProfile 5 where
  denominator := 1000000000000000
  denominator_pos := by norm_num
  count := ![0, 1362678630945, 498637780779522, 498636844034842, 1362696554691]
  count_sum := by norm_num [Fin.sum_univ_succ]

def regionalProfile : Fin 3 → IntegerZSplitProfile 5 := ![region0, region1, region2]

/-- Released object-150 rotation weights rounded half-up to 10^15; they sum to 1000000000000001, so the
exact normalized weights are these integers over 1000000000000001. -/
def regionalWeight : Fin 3 → ℕ := ![86974611, 552127551170202, 447872361855188]

end MME.DWZPositiveComponent125


