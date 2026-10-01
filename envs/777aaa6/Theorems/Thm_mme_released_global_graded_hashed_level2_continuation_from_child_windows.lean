-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_level2_continuation_from_child_windows
-- name    : mme_released_global_graded_hashed_level2_continuation_from_child_windows
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:26:32.785134+00:00
-- url     : https://prove2.me/theorems/fe68374b-2f02-46f9-904e-d0b4b4de5d83
-- title:
--   Level-2 continuation from the six regional child windows
-- statement:
--   This is the level-2 continuation of the hashed construction, with the level-3 stage already fixed to the proved square-scale tolerance stages. Its source predicate is the conjunction of the six regional child windows.
--
--   **Setting.** Let $D=10^{12}$, $\mathrm{blocks}(K)=D^5K$ and $n=6\,\mathrm{blocks}(k^2)$. For a family $a$ of released global references at scale $K$, let $N_K(a)=\texttt{partSize}\,K\,a\,1$ be the number of hashed positions.
--
--   For a region $r\in\mathrm{Fin}\,6$, a released positive integer frame $F_r$ (`ReleasedPositiveInteger.Frame r K`) fixes a reference address $F_r.\mathrm{ref}$ and a physical position map $F_r.\mathrm{pos}$ for the region's $\mathrm{blocks}_r(K)\cdot 4$ level-2 positions. Let $\sigma_r$ be the released mode convention `roleEquiv r`. Given a word $y$ on the $N_K(a)$ hashed positions and a bijection $E:\bigsqcup_r\mathrm{Fin}(\mathrm{blocks}_r(K)\cdot4)\simeq\mathrm{Fin}\,N_K(a)$, let $y_r=y\circ E(r,\cdot)$ and $f_r=\mathrm{split}(F_r.\mathrm{pos},y_r)$. The **window predicate** $\mathcal W_\delta(i,y)$ says that for every region $r$, with $j=\sigma_r^{-1}(i)$:
--
--   1. $f_r$ is graded in mode $j$ with respect to $F_r.\mathrm{ref}$ (`RecursiveYZ.Graded`), and
--   2. for every cell $c$ and complete level-2 word $w$,
--   $$\Big|\,\mathrm{freq}\big(\mathrm{count}(\mathrm{fullCell}(F_r.\mathrm{ref}),f_r)\big)(c,w)-\mathrm{freq}\big(K\cdot\mu^{(3)}_{r,j}\big)(c,w)\Big|\le\delta ,$$
--   where $\mathrm{freq}(\mu)(c,w)=\mu(c,w)/\sum_v\mu(c,v)$ and $\mu^{(3)}_{r}$ is the released level-3 child profile `RecStage.mu3 r`.
--
--   This is exactly the target `childWindow (frame.step …) δ` of [the square-scale graded tolerance stages](p2m:theorem/fc1dbf49-3f36-489b-a834-488bae3a56fe) for region $r$, reoriented by $\sigma_r^{-1}$.
--
--   **Claim.** There is $\delta_0>0$ such that for every $\delta\in(0,\delta_0]$ there is $C\in\mathbb N$ with the following property. For every $k_0$ there are $k\ge k_0$, a reference family $a$ at scale $K=k^2$ and frames $F_r$ at scale $K$ ($r\in\mathrm{Fin}\,6$), such that for **every** bijection $E$ as above there is a graded logarithmic joint recipe $R'$ (`LogJointRecipeG`) of level $2$ on $N_K(a)$ positions with source $\mathcal W_\delta$ satisfying
--
--   - $1\le\mathrm{inputs}(R')\le(k+1)^C$ and $1\le R'.a\,R'.b\,R'.c$;
--   - $n\cdot0.5859676\le\mathrm{logOutputs}(R')$;
--   - $n\cdot5.83785872051\le\log(R'.a\,R'.b\,R'.c)$.
--
--   **Remarks.** The quantifier over all $E$ is harmless. A recipe for one bijection $E_0$ becomes one for any $E$ by a one-part `partition` that relabels positions, with the same inputs, outputs and dimensions. The rate share $0.5859676$ lies below the proved level-2 margin, which is $0.585967670317$ per $n$ (theorem 7fd711a3). The dimension target is the full hashed target, because a stage does not change dimensions. The intended proof follows the mission plan (WP6/WP7): split the level-2 positions into zero and positive halves, which the grading fixes; close the zero halves with an exact-profile boundary end; apply the single-type graded step to the positive halves; finish with a level-1 boundary. The tolerance $\delta_0$ may be taken as small as the continuity of the level-2 rate needs.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); level-2 part (WP6/WP7) of marwahaha's plan comment of 2026-09-24; child windows from BrunoDCDO's square-scale graded tolerance stages fc1dbf49 and positive source inclusion 0f51d84d; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv 2404.16349.

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
import Definitions.Def_mme_regional_tolerance_window_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_level2_continuation_from_child_windows :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∃ (a : ∀ o : Fin 6, Reference o (k^2))
          (frame : ∀ r : Fin 6, ReleasedPositiveInteger.Frame r (k^2)),
        ∀ E : ((r : Fin 6) × Fin (ReleasedJointInterior.blocks r (k^2) * 4)) ≃
            Fin (partSize (k^2) a 1),
        ∃ next : LogJointRecipeG (partSize (k^2) a 1) 2 (fun i y ↦ ∀ r : Fin 6,
            RecursiveYZ.Graded (RecStage.htotal3 r) ((ReleasedJointInterior.roleEquiv r).symm i)
              (frame r).reference
              (ProfiledCW.split (ell := 2) (frame r).positions
                (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩))) ∧
            ∀ c w, |cellFrequency (RecursiveYZ.count (fullCell (RecStage.htotal3 r) (frame r).reference)
                (ProfiledCW.split (ell := 2) (frame r).positions
                  (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩)))) c w -
              cellFrequency (fun c w ↦ k^2 * RecStage.mu3 r ((ReleasedJointInterior.roleEquiv r).symm i) c w) c w| ≤ δ),
          1 ≤ next.inputs ∧
          next.inputs ≤ (k + 1) ^ C ∧
          1 ≤ next.a * next.b * next.c ∧
          (6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000) ≤ next.logOutputs ∧
          (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
            Real.log ((next.a * next.b * next.c : ℕ) : ℝ) := by sorry
