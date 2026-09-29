-- Prove2me | Theorems.Thm_mme_released_boundary_unit_factor_mass_entropy_certificate
-- name    : mme_released_boundary_unit_factor_mass_entropy_certificate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:18:58.637097+00:00
-- url     : https://prove2.me/theorems/559ea2ba-268f-4f01-aae2-0c884191b944
-- title:
--   Boundary unit factor: entropy certificate
-- statement:
--   This is the numerical certificate for the unit-scale boundary dimension factor of the released global candidate, in entropy form, with the Stirling-type error made explicit.
--
--   Let $D=10^{12}$ be the released denominator, so that $\mathrm{blocks}(1)=D^5=10^{60}$. For each of the $144$ boundary cells $c$ (an owner $o\in\mathrm{Fin}\,6$ together with a level-3 shape having a zero coordinate), let $z(c,s)=z_1(c,s)$, for words $s$ of four letters in $\{0,1,2\}$, be the released unit-scale histogram of the cell in the mode following its zero mode. Let $N_c=\sum_s z(c,s)$, and let $\mathrm{ones}(s)$ be the number of letters of $s$ equal to $1$. Write
--
--   $$
--   \mathcal H_c\;=\;N_c\log N_c-\sum_s z(c,s)\log z(c,s)
--   $$
--
--   for the mass entropy of the histogram (with $0\log0=0$).
--
--   **Claim.**
--
--   $$
--   6D^5\cdot 0.450512205\;+\;\sum_c 81\,\log\bigl(6(N_c+1)\bigr)\;\le\;\sum_c\Bigl(\mathcal H_c+\log 5\sum_s z(c,s)\,\mathrm{ones}(s)\Bigr).
--   $$
--
--   **Numerical evidence.** With the exact released integers (the largest $N_c$ is about $1.25\cdot10^{58}$) and 90-digit arithmetic, the right side divided by $6D^5$ is $0.45051220582308506909\ldots$, the error sum on the left is about $1.53\cdot10^{6}$, and the right side exceeds the left by $4.94\cdot10^{51}$, a relative margin of $1.83\cdot10^{-9}$.
--
--   **Role.** Together with the [multinomial entropy lower bound](p2m:theorem/69879847-c4f7-4e58-96b4-b3ba44424367) applied to every cell ($81$ is the number of words), this implies the [boundary unit factor bound](p2m:theorem/1e6f06b7-d9ba-4462-af69-0d03251d1f30) $6D^5\cdot0.450512205\le\log B$. It contains no factorials: it only asks for explicit logarithms of explicit integers, which can be certified with rational log-series bounds such as [the rational log series certificate](p2m:theorem/b483c263-a8af-4620-9b3c-1d34a5d7256b) and [rational entropy log bounds](p2m:theorem/55f619f2-df10-4489-9ff1-88875ed4ccc1).
--
--   **Formalization Note.** $z(c,s)$ is `zCountAt 1 c s`, i.e. the global weight times the joint row counts (`wordCounts`), and $\mathcal H_c$ is `MME.RegionRate.massEntropy (fun s => (zCountAt 1 c s : ℝ))`. For a cell with one zero grade both nonzero modes carry the same histogram up to the relabelling $s\mapsto 2-s$, which preserves $\mathrm{ones}$ and the entropy; so the value does not depend on the `choose` in `zMode`.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134), WP7 boundary part of the dimension certificate; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3; reduction of mme_released_boundary_unit_factor_log_lower (1e6f06b7).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_entropy_rate_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_boundary_unit_factor_mass_entropy_certificate :
    (6 * blocks 1 : ℝ) * ((450512205 : ℝ)/1000000000) +
        ∑ c : Fin zCells, 81 * Real.log (6 * (((∑ s, zCountAt 1 c s : ℕ) : ℝ) + 1)) ≤
      ∑ c : Fin zCells, (MME.RegionRate.massEntropy (fun s => (zCountAt 1 c s : ℝ)) +
        ((∑ s, zCountAt 1 c s * Boundary.ones s : ℕ) : ℝ) * Real.log 5) := by sorry
