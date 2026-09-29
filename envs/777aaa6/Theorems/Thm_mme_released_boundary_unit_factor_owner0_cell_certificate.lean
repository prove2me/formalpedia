-- Prove2me | Theorems.Thm_mme_released_boundary_unit_factor_owner0_cell_certificate
-- name    : mme_released_boundary_unit_factor_owner0_cell_certificate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:51:13.426177+00:00
-- url     : https://prove2.me/theorems/cf2cc414-0cc9-4150-ac26-b3ac280d9b19
-- title:
--   Boundary unit factor: owner 0 cell certificate
-- statement:
--   This is the per-cell part of the numerical certificate for the unit-scale boundary dimension factor of the released global candidate, for owner $o=0$.
--
--   Fix the owner $o=0$. For a level-3 shape $s=(s_0,s_1,s_2)$ (one of the $45$ triples of naturals with $s_0+s_1+s_2=8$) and a mode $m\in\{0,1,2\}$, let $h_{s,m}(w)=\mathrm{wordCounts}(o,m,s,w)$ be the released unit-scale histogram of the joint rows of the cell $s$ in mode $m$, over the $81$ words $w\in\{0,1,2\}^4$; it equals $\alpha_{o,s}$ times an integer histogram of total mass $10^{48}$, where $\alpha_{o,s}$ is the released global weight of the cell. Put $N=\sum_w h_{s,m}(w)$, let $\mathrm{ones}(w)$ be the number of letters of $w$ equal to $1$, and write
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

theorem mme_released_boundary_unit_factor_owner0_cell_certificate :
    ∀ s : Fin 45, ∀ j : Fin 3, ((shape s).val (hashMode 0 j)).val = 0 →
      (((([-11340, 49606893915445719198461070679999999999999999999999988660, 2486788621622298821331363268367503311298889999999999988660, 30163129815856621649377093749182801880914099999999999988660, 85574225979056657351621200612563075095757279999999999988660, 30069522158859732287680082399129808096423039999999999988660, 2518371893967097279590093203887643268633819999999999988660, 50007291508199833291808492839999999999999999999999988660, -11340, 49279954673771419192644115829999999999999999999999988660, 0, 0, 0, 0, 0, 0, 49221705655444438028827696989999999999999999999999988660, 2462660104500596615938760253704640129289549999999999988660, 0, 0, 0, 0, 0, 2502501836857948990852731276199358029223869999999999988660, 29847986703404827696236194183670996301812039999999999988660, 0, 0, 0, 0, 29841607991467784090409571000222970160476539999999999988660, 85529917414588362616297686785251098115733419999999999988660, 0, 0, 0, 83916707382837509651986004145185151104693759999999999988660, 30295306029754504779424659434516386011563679999999999988660, 0, 0, 29916765458934431664221146973013952262160059999999999988660, 2562729051506958265067415346049268880212629999999999988660, 0, 2532605850899428989106110460220609556253899999999999988660, 50115012049292282823206908219999999999999999999999988660, 49741369341473278212169938469999999999999999999999988660, -11340] : List ℤ).getD s.val 0 : ℤ)) : ℝ) ≤
        MME.RegionRate.massEntropy
            (fun w => (wordCounts 0 (hashMode 0 (j + 1)) (shape s) w : ℝ)) +
          ((∑ w, wordCounts 0 (hashMode 0 (j + 1)) (shape s) w * Boundary.ones w : ℕ) : ℝ) *
            Real.log 5 -
          81 * Real.log (6 * (((∑ w, wordCounts 0 (hashMode 0 (j + 1)) (shape s) w : ℕ) : ℝ) + 1)) := by sorry
