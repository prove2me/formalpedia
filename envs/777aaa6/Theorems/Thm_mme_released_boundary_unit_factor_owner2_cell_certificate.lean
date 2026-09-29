-- Prove2me | Theorems.Thm_mme_released_boundary_unit_factor_owner2_cell_certificate
-- name    : mme_released_boundary_unit_factor_owner2_cell_certificate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T01:51:11.827888+00:00
-- url     : https://prove2.me/theorems/7a448795-eb76-4efb-9f94-e9da594b2ada
-- title:
--   Boundary unit factor: owner 2 cell certificate
-- statement:
--   This is the per-cell part of the numerical certificate for the unit-scale boundary dimension factor of the released global candidate, for owner $o=2$.
--
--   Fix the owner $o=2$. For a level-3 shape $s=(s_0,s_1,s_2)$ (one of the $45$ triples of naturals with $s_0+s_1+s_2=8$) and a mode $m\in\{0,1,2\}$, let $h_{s,m}(w)=\mathrm{wordCounts}(o,m,s,w)$ be the released unit-scale histogram of the joint rows of the cell $s$ in mode $m$, over the $81$ words $w\in\{0,1,2\}^4$; it equals $\alpha_{o,s}$ times an integer histogram of total mass $10^{48}$, where $\alpha_{o,s}$ is the released global weight of the cell. Put $N=\sum_w h_{s,m}(w)$, let $\mathrm{ones}(w)$ be the number of letters of $w$ equal to $1$, and write
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

theorem mme_released_boundary_unit_factor_owner2_cell_certificate :
    ∀ s : Fin 45, ∀ j : Fin 3, ((shape s).val (hashMode 2 j)).val = 0 →
      (((([-11340, 49580151013439703931572098709999999999999999999999988660, 2486893764560018963970104130058952820422339999999999988660, 30162367654353020212972468670683014256158749999999999988660, 85581298089989961896458237802960159296882569999999999988660, 30068911217502217135244927188221925341405639999999999988660, 2518251968511296967078923950158079471737979999999999988660, 49951019673173397672536346599999999999999999999999988660, -11340, 49419391032443983390845885779999999999999999999999988660, 0, 0, 0, 0, 0, 0, 49254970266609980038857398429999999999999999999999988660, 2460953691290406760970414300825179216301199999999999988660, 0, 0, 0, 0, 0, 2503308762944852365226536725056509036600799999999999988660, 29847430147478584071690837613390013843088599999999999988660, 0, 0, 0, 0, 29843034277405315379867043118452700952939369999999999988660, 85538626345252092133542481343648040614247299999999999988660, 0, 0, 0, 83898043062272313176017069006111743786819839999999999988660, 30296172800485362394679903171172993694509119999999999988660, 0, 0, 29916272233810718630015652130402349699358329999999999988660, 2563639178890112808177053427990547517297009999999999988660, 0, 2532488064087034492338601729973458953931679999999999988660, 50129517384960830590908980839999999999999999999999988660, 49757258705452207861053001909999999999999999999999988660, -11340] : List ℤ).getD s.val 0 : ℤ)) : ℝ) ≤
        MME.RegionRate.massEntropy
            (fun w => (wordCounts 2 (hashMode 2 (j + 1)) (shape s) w : ℝ)) +
          ((∑ w, wordCounts 2 (hashMode 2 (j + 1)) (shape s) w * Boundary.ones w : ℕ) : ℝ) *
            Real.log 5 -
          81 * Real.log (6 * (((∑ w, wordCounts 2 (hashMode 2 (j + 1)) (shape s) w : ℕ) : ℝ) + 1)) := by sorry
