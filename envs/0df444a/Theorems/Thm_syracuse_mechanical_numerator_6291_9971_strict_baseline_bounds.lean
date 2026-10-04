-- Prove2me | Theorems.Thm_syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds
-- name    : syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T20:19:01.217169+00:00
-- url     : https://prove2.me/theorems/ab3539bc-2660-453c-ac0c-d3f902b3d85c
-- title:
--   Strict exact6291/9971 mechanical numerator bounds between2403660 and2403661 times the positive power gap
-- statement:
--   Define the natural-number arithmetic sum M = sum over j=0,...,6290 of 3^(6291-1-j) * 2^floor(9971*j/6291), and the natural power gap D = 2^9971 - 3^6291. The exact conclusion is 3^6291 < 2^9971 and 2403660*D < M and M < 2403661*D. Thus the gap is strictly positive and both numerator bounds are strict. No hypothesis is supplied and no Syracuse trajectory, cycle, word realization or baseline theorem is assumed. The Syracuse prefix and baseline wording describe research context only; the type is Mathlib-only arithmetic. In particular2403661 is not thereby a proved cycle-exclusion or descent baseline. This new source-only submission packet requires independent whole-packet review and fresh kernel verification; neither prior source review nor historical source-pattern acceptance transfers acceptance or runtime authority.
-- source:
--   Task114 source-only assembly from C:/Users/jason/prove2me/cycle_mechanical_margin_6291_9971_draft_01.lean (175 lines), its68-line explanation,557-line preparation and actual completed independent Task105 peer review. All five definitions and eleven theorem bodies, the sole new large ordinary decide+kernel obligation, binary fuel14 and copied options are retained byte-for-byte inside fresh namespace CollatzMechanicalMargin6291_9971Submission01. An outside solution uses the reviewed full bounds; the expanded public sum spells the exponent6291-1-j, definitionally equal to the retained6290-j. No private evaluator alias appears in the public preamble/type. Task105 assembly was inline and had no external utility. Its exact prior copy regions, APIs, provenance and actual review are bound without candidate or arithmetic reevaluation. No Step, Offset, canonicalC, community theorem, Open/prospective baseline, target or Solutions import is used. Historical fixed5626 acceptance is source-pattern provenance only. Task106/109 and all prior artifacts are preserved; no client, executed API request, new review verdict, ledger, reservation or public action is supplied.

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds :
    (3 : ℕ) ^ 6291 < 2 ^ 9971 ∧
      2403660 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) <
        (∑ j ∈ Finset.range 6291,
          (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291)) ∧
      (∑ j ∈ Finset.range 6291,
        (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291)) <
        2403661 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) := by sorry
