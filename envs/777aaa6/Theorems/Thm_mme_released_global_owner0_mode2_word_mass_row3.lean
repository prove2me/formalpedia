-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_word_mass_row3
-- name    : mme_released_global_owner0_mode2_word_mass_row3
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:19:43.11071+00:00
-- url     : https://prove2.me/theorems/7f3de7d3-6187-45e0-8573-711c6e2eac0c
-- title:
--   owner0 mode2 word mass row3
-- statement:
--   Fix owner 0, mode 2, and coordinate pool 3. Let $N_{3,w}$ be the stated table entry, $D=10^{12}$, $\alpha_s$ the outer cell weight, and $c_{s,a}$ the integer atom multiplicity. For every four-letter word $w$,
--
--   $$\frac{N_{3,w}}{D^5}=\sum_{s:\,\operatorname{shape}(s)_{2}=3}\frac{\alpha_s}{D^5}\sum_{a:\,a_{2}=w}c_{s,a}.$$
--
--   This identifies the rational table with the actual released masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_word_mass_row3 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 2308306613040706423952098332634472500000000000000000000000, 0, 2308306613007111103264098332634472500000000000000000000000, 0, 0, 0, 2700725590264062800349693746132600304344832772500000000000, 0, 80610140962175658003557424913264706391310334455000000000000, 0, 2700725590283070549037693746132600304344832772500000000000, 0, 0, 0, 2700725197352111196844837227146643335685494926000000000000, 0, 2700725197337855385328837227146643335685494926000000000000, 0, 0, 0, 0, 0, 0, 0, 2700725590268814737521693746132600304344832772500000000000, 0, 80610140955911978152169424913264706391310334455000000000000, 0, 2700725590264062800349693746132600304344832772500000000000, 0, 0, 0, 80610163806403253245519228384543060828629010148000000000000, 0, 80610163806031975487411228384543060828629010148000000000000, 0, 0, 0, 0, 0, 2308279250865353833958186422999273000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2700725197337855385328837227146643335685494926000000000000, 0, 2700725197337855385328837227146643335685494926000000000000, 0, 0, 0, 0, 0, 2308279251118275510078186422999273000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 3 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
