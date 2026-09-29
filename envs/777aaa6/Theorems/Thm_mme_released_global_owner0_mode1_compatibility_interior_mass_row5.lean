-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode1_compatibility_interior_mass_row5
-- name    : mme_released_global_owner0_mode1_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:20:48.438304+00:00
-- url     : https://prove2.me/theorems/e37d2de4-d9d2-4b34-a365-35e9f71d374b
-- title:
--   owner0 mode1 compatibility interior mass row5
-- statement:
--   Fix owner 0, mode 1, and coordinate pool 5. Let $N_{5,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{5,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{1}=5,\ \operatorname{shape}(s)_{2}\ne0}\frac{\alpha_s}{D^5}\sum_{a:\,a_{1}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the compatibility entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode1_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114185117191404110647072217067584500000000000000000000000, 0, 0, 0, 0, 0, 136875021933329342240427836260518093587618295500000000000, 0, 136875021933329342240427836260518093587618295500000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 114185117077357618519072217067584500000000000000000000000, 0, 0, 0, 0, 0, 5662109468851146773631266097442592812824763409000000000000, 0, 5662109469141014941123266097442592812824763409000000000000, 0, 0, 0, 136874988789473978245875282923840871564107773500000000000, 0, 5662109175666560237853787459993766756871784453000000000000, 0, 136874988794225915417875282923840871564107773500000000000, 0, 0, 0, 0, 0, 0, 0, 136875021933329342240427836260518093587618295500000000000, 0, 136875021947585153756427836260518093587618295500000000000, 0, 0, 0, 136874988808481726933875282923840871564107773500000000000, 0, 5662109181848830498625787459993766756871784453000000000000, 0, 136874988789473978245875282923840871564107773500000000000, 0, 0, 0, 114184624651980457311267987127338000000000000000000000000, 0, 114184624642476582967267987127338000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 5 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
