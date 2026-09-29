-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_word_mass_row5
-- name    : mme_released_global_owner0_mode1_word_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T23:54:00.849593+00:00
-- url     : https://prove2.me/theorems/19e07a1b-af8e-455c-87e3-7c3a94cc1261
-- title:
--   Outer word mass table identity, owner 0 mode 1 pool 5
-- statement:
--   Fix the released profile with owner 0 and coordinate mode 1. Let $D=10^{12}$ be its common denominator, $\alpha_s$ the outer weight of cell $s$, and $c_{s,a}$ the integer multiplicity of supported atom $a$. For every four-letter word $w$, the certified table entry $N_{5,w}$ satisfies
--
--   $$\frac{N_{5,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_1=5}\frac{\alpha_s}{D^5}\sum_{a:\,a_1=w}c_{s,a}.$$
--
--   This identifies coordinate pool 5 of the rational entropy table with the actual released word masses. The table entries are fixed explicitly in the formal statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_word_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170678953676709220225072217067584500000000000000000000000, 0, 0, 0, 0, 0, 189265998603008664050427836260518093587618295500000000000, 0, 189265998603008664050427836260518093587618295500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170678953704235119637072217067584500000000000000000000000, 0, 0, 0, 0, 0, 6680603540788812748261266097442592812824763409000000000000, 0, 6680603542239574526381266097442592812824763409000000000000, 0, 0, 0, 189265971060700925321875282923840871564107773500000000000, 0, 6680603275409043910939787459993766756871784453000000000000, 0, 189265970994666666723875282923840871564107773500000000000, 0, 0, 0, 0, 0, 0, 0, 189265998603008664050427836260518093587618295500000000000, 0, 189265998612545395848427836260518093587618295500000000000, 0, 0, 0, 189265971060832355137875282923840871564107773500000000000, 0, 6680603281327045707503787459993766756871784453000000000000, 0, 189265971055981845603875282923840871564107773500000000000, 0, 0, 0, 170678557123367031009267987127338000000000000000000000000, 0, 170678557137458555255267987127338000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD
      (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) /
      1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 5 then
      ((alpha 0 s * ((jointRows 0 s).map
        (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 else 0 := by sorry
