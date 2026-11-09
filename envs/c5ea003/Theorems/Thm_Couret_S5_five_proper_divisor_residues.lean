-- Prove2me | Theorems.Thm_Couret_S5_five_proper_divisor_residues
-- name    : Couret.S5.five_proper_divisor_residues
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:29.204763+00:00
-- url     : https://prove2.me/theorems/cf88f9de-30f4-4c85-b92a-b18ad83e1945
-- title:
--   Strict divisors of 64141 realize exactly seven unit residues
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For every $u\in C$,
--
--   $$\exists d\mid64141:\ 1<d<64141,\ d\equiv\rho(u)\pmod {30}\quad\iff\quad\rho(u)\ne1.$$
--
--   This is a concrete arithmetic witness whose strict-divisor residue support omits exactly residue one.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/OptimalFive.lean, lines 59–63; source file SHA-256 10e4872f2ae446d57ad6e2c526d92085da7cdb70df9bb99e2641c0da1b7e7c1f; theorem Couret.S5.five_proper_divisor_residues

import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
import Std
import Theorems.Thm_Couret_maskRun_correct
import Theorems.Thm_Couret_mask_254_omits_only_residue_one
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem five_proper_divisor_residues (u : Code30) :
    (∃ d : Nat, d ∣ 64141 ∧ 1 < d ∧ d < 64141 ∧ d % 30 = residue30 u) ↔ residue30 u ≠ 1 := by sorry












end S5
end Couret
