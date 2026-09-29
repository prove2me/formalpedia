-- Prove2me | Theorems.Thm_mme_released_boundary_unit_factor_log_lower
-- name    : mme_released_boundary_unit_factor_log_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:51:08.687978+00:00
-- url     : https://prove2.me/theorems/1e6f06b7-d9ba-4462-af69-0d03251d1f30
-- title:
--   Lower bound for the log of the unit-scale boundary factor
-- statement:
--   This is a numerical lower bound for the logarithm of the unit-scale boundary dimension factor of the released global candidate.
--
--   Let $D=10^{12}$ be the released denominator, so that $\mathrm{blocks}(1)=D^5=10^{60}$. For each of the $144$ boundary cells $c$ (an owner $o\in\mathrm{Fin}\,6$ together with a level-3 shape having a zero coordinate), let $z(c,s)=z_1(c,s)$, for words $s$, be the released unit-scale histogram of the cell in the mode following its zero mode, and let $N_c=\sum_s z(c,s)$. For a word $s$ let $\mathrm{ones}(s)$ be the number of letters of $s$ equal to $1$. The unit-scale boundary dimension factor is
--
--   $$
--   B=\prod_{c}\binom{N_c}{(z(c,s))_s}\,5^{\sum_s z(c,s)\,\mathrm{ones}(s)}.
--   $$
--
--   **Claim.**
--
--   $$
--   6\,D^5\cdot 0.450512205\ \le\ \log B .
--   $$
--
--   **Role.** $B$ is the dimension contributed by the level-3 zero cells, the boundary blocks closed by the exact-profile boundary end. It enters the [hashed construction at a chosen reference](p2m:theorem/71693563-1700-4744-b3a2-7f624e7357ee) only through $k^2\log B$. This lemma is the level-3 boundary part of the dimension certificate (WP7 in the mission plan): a single fixed numerical fact. A computation with the exact released integers and 80-digit log-gamma gives $\log B/(6D^5)=0.4505122058230850\ldots$, so the stated constant leaves a relative margin of about $1.8\cdot10^{-9}$, which is $4.9\cdot10^{51}$ in absolute terms. Stirling-type error terms are of order $10^{4}$.
--
--   **Formalization Note.** $B$ is the natural number `∏ c : Fin zCells, ((∑ s, zCountAt 1 c s)! / ∏ s, (zCountAt 1 c s)!) * 5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s)`, cast to `ℝ`. The division is exact. `zCountAt 1 c s` is `wordCounts`, the global weight times the joint row counts, so every entry is an explicit integer of size at most $10^{60}$. A cell with two zero grades contributes a factor $1$ whichever zero mode is chosen, and for a cell with one zero grade both nonzero modes give the same factor, so the value does not depend on the `choose` in `zMode`.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); marwahaha's plan comment of 2026-09-24 (WP7 dimension certificate: level-3 zero cells); boundary factor B as in theorem 71693563-1700-4744-b3a2-7f624e7357ee and 8a1dbc6c-de97-4a8b-b66f-e831372553f2; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_boundary_unit_factor_log_lower :
    (6 * blocks 1 : ℝ) * ((450512205 : ℝ)/1000000000) ≤
      Real.log ((∏ c : Fin zCells,
        ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
        5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) := by sorry
