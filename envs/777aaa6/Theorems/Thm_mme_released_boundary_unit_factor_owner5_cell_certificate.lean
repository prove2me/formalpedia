-- Prove2me | Theorems.Thm_mme_released_boundary_unit_factor_owner5_cell_certificate
-- name    : mme_released_boundary_unit_factor_owner5_cell_certificate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:50:42.22887+00:00
-- url     : https://prove2.me/theorems/07751cd6-9a07-4203-bc03-348cf3c0843c
-- title:
--   Boundary unit factor: owner 5 cell certificate
-- statement:
--   This is the per-cell part of the numerical certificate for the unit-scale boundary dimension factor of the released global candidate, for owner $o=5$.
--
--   Fix the owner $o=5$. For a level-3 shape $s=(s_0,s_1,s_2)$ (one of the $45$ triples of naturals with $s_0+s_1+s_2=8$) and a mode $m\in\{0,1,2\}$, let $h_{s,m}(w)=\mathrm{wordCounts}(o,m,s,w)$ be the released unit-scale histogram of the joint rows of the cell $s$ in mode $m$, over the $81$ words $w\in\{0,1,2\}^4$; it equals $\alpha_{o,s}$ times an integer histogram of total mass $10^{48}$, where $\alpha_{o,s}$ is the released global weight of the cell. Put $N=\sum_w h_{s,m}(w)$, let $\mathrm{ones}(w)$ be the number of letters of $w$ equal to $1$, and write
--
--   $$
--   \mathcal H(h)\;=\;N\log N-\sum_w h(w)\log h(w)
--   $$
--
--   for the mass entropy (with $0\log 0=0$). Let $\pi_o$ be the owner's hash orientation (`hashMode o`).
--
--   **Claim.** For every shape index $s$ and every mode $j$ such that the coordinate $\pi_o(j)$ of $s$ is zero, with $m=\pi_o(j+1)$,
--
--   $$
--   g_{o,s}\;\le\;\mathcal H(h_{s,m})\;+\;\log 5\sum_w h_{s,m}(w)\,\mathrm{ones}(w)\;-\;81\log\bigl(6(N+1)\bigr),
--   $$
--
--   where $g_{o,s}$ is the explicit integer listed in the formal statement (entry $s$ of the list; entries of shapes without a zero coordinate are $0$ and unused).
--
--   **Numerical evidence.** The integers $g_{o,s}$ were obtained from rigorous rational upper bounds for $\log(h(w)/N)$ (the series $\log x=2\,\mathrm{artanh}\frac{x-1}{x+1}$ with $14$ terms after scaling by a power of $2$, rounded outward at $10^{-20}$), the rational bound $\log 5\ge 1.6094379124340\ldots$, and the crude bound $81\log(6(N+1))\le 81\cdot 60\log 10\le 11340$. Recomputing the right side with 80-digit arithmetic, every cell exceeds its $g_{o,s}$, the smallest excess (over all owners) being about $1.29\cdot10^{3}$. The corner cells $s\in\{(0,0,8),(0,8,0),(8,0,0)\}$ carry a point-mass histogram and get $g=-11340$.
--
--   **Role.** Summing these six owner certificates over the $144$ boundary cells gives $\sum g_{o,s}=6\cdot10^{60}\cdot0.450512205+4.94\cdot10^{51}$, which proves the [entropy certificate for the boundary unit factor](p2m:theorem/559ea2ba-268f-4f01-aae2-0c884191b944).
--
--   **Formalization Note.** The histogram is `wordCounts o (hashMode o (j + 1)) (shape s) w`, which is exactly `zCountAt 1 c w` for the boundary cell $c=(o,\mathrm{shape}\,s)$ when $j$ is its chosen zero mode; for shapes with two zero coordinates every choice gives a point mass. $\mathcal H$ is `MME.RegionRate.massEntropy`. The bound $g_{o,s}$ is written as `(L : List ℤ).getD s.val 0`.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134), WP7 boundary part of the dimension certificate; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, arXiv 2404.16349v3; per-owner split of mme_released_boundary_unit_factor_mass_entropy_certificate (559ea2ba).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_entropy_rate_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_boundary_unit_factor_owner5_cell_certificate :
    ∀ s : Fin 45, ∀ j : Fin 3, ((shape s).val (hashMode 5 j)).val = 0 →
      (((([-11340, 49647854562822021062936584709999999999999999999999988660, 2487425428959939401378355318296425581411419999999999988660, 30161682257883694453350544244616051167891279999999999988660, 85580652520383582397820180244103152249471939999999999988660, 30068852496475951581636157442495102320129719999999999988660, 2518420453886711974300012073602862242415999999999999988660, 49984871447864556238218589599999999999999999999999988660, -11340, 49396635450094068305454530219999999999999999999999988660, 0, 0, 0, 0, 0, 0, 49298498256544717557385096729999999999999999999999988660, 2462054477285195681676314770782280761522879999999999988660, 0, 0, 0, 0, 0, 2502852454791072595235767281592364347704719999999999988660, 29848185450281218845379557609190308401753939999999999988660, 0, 0, 0, 0, 29843118026376970581534775822377866097932039999999999988660, 85535730403671050936264895952289400036129259999999999988660, 0, 0, 0, 83899420204873682610878431045872375614233319999999999988660, 30295651400233216821355244349918751852833639999999999988660, 0, 0, 29918250959723185586773827108523333964389039999999999988660, 2562399822100859843003888043678234338633639999999999988660, 0, 2531327790857691225557930110190465957593509999999999988660, 49892168512659432183790535649999999999999999999999988660, 49891812020518879275001492559999999999999999999999988660, -11340] : List ℤ).getD s.val 0 : ℤ)) : ℝ) ≤
        MME.RegionRate.massEntropy
            (fun w => (wordCounts 5 (hashMode 5 (j + 1)) (shape s) w : ℝ)) +
          ((∑ w, wordCounts 5 (hashMode 5 (j + 1)) (shape s) w * Boundary.ones w : ℕ) : ℝ) *
            Real.log 5 -
          81 * Real.log (6 * (((∑ w, wordCounts 5 (hashMode 5 (j + 1)) (shape s) w : ℕ) : ℝ) + 1)) := by sorry
