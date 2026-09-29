-- Prove2me | Theorems.Thm_mme_released_level2_pooled_positive_recipe
-- name    : mme_released_level2_pooled_positive_recipe
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:50:28.632461+00:00
-- url     : https://prove2.me/theorems/089fbb5d-a337-4731-9e66-0514247f1174
-- title:
--   Pooled level-2 step with its level-1 boundary
-- statement:
--   This is the pooled level-2 step of the released recursion followed by its level-1 boundary. It involves only the level-2 data `RecStage.parent2, n2, m2, mu2`: one region per positive level-2 term, $1104$ regions in all.
--
--   **Setting.** Let $D=10^{12}$. For a region $r<1104$ let $a_r$ (`parent2 r`) be its grade triple, which has total $4$ and three positive entries. Let $n_2(r)=w_r D^2$ be its block count, where $w_r>0$ is its table weight. Let $m_2(r,e)=w_r\,j(a_r,s_r,e)\,D$ be its level-1 split counts, and let $\mu_2$ be the induced level-1 histograms. At scale $t$ the positions are $\mathrm{Position}(t\,n_2)$ in the canonical layout `positionsAt n2 t`, one fine letter per half, so there are $\mathrm{len}_t=\sum_r 2t\,n_2(r)$ fine positions. Let
--   $$\tau_t=\sqrt{\frac{8\cdot 25\cdot 1104\cdot 3^2\,(\lfloor\sqrt t\rfloor+2)}{t}} .$$
--   The source $S_t$ holds in mode $i$ for a word $x$ when:
--   - $x$ is parent-graded: in every block of region $r$, the two letters sum to $a_r(i)$;
--   - $x$ is `parentTypical` at tolerance $\tau_t$ for $(t\,n_2,\ t\,m_2,\ t\,\mu_2(i))$: every joint pair frequency in every region is within $\tau_t$ of the region's mixture.
--
--   **Claim.** There is $C\in\mathbb N$ such that for all sufficiently large $t$ there is a graded logarithmic joint recipe $R$ (`LogJointRecipeG`) of level $2$ on $\mathrm{len}_t$ positions with source $S_t$ satisfying
--   $$1\le\mathrm{inputs}(R)\le(t+1)^C,\qquad 1\le abc,\qquad 585967670317\cdot 6\cdot10^{48}\,t\le\mathrm{logOutputs}(R),\qquad 37468424\cdot 6\cdot10^{53}\,t\le\log(abc),$$
--   where $(a,b,c)$ are the dimensions of $R$.
--
--   **Why it should hold.**
--   - **Stage.** One `stage` from level 2 to level 1 with a single part: the [graded band part stage](p2m:theorem/5d673b53-781e-4970-a100-af61d306eba4) at $\ell=1$ with $n=n_2$ and $R=1104$. It uses one target address $a$ and the exact goodness predicate $\mu''=t\mu_2(i)$. Its rate $c\,t$ uses $c=585967670317\cdot6\cdot10^{48}<\mathrm{regionalRate}(n_2,m_2,\mu_2)$, which is [the level-2 margin](p2m:theorem/7fd711a3-4eda-4e33-8846-d98960c41db8). The hypotheses $\sum_e m_2(r,e)=n_2(r)$ (because $\sum_e j=D$ for the three positive shapes) and $n_2(r)>0$ are finite data checks. The type count is polynomial in $t$.
--   - **Boundary.** Every level-1 cell $(r,e)$ has a zero coordinate. Given the address, its letters are forced. So the [exact-profile boundary end](p2m:theorem/2c6d3aa4-183c-4680-b806-283597581306) at $\ell=1$ closes the recipe, and its multinomials are all $1$. Hence $abc=5^{t\,U}$ with $U=\sum_r 2D\,w_r(D-s_r)$, the unit count of level-1 letters of type $(0,1,1)$ up to order.
--   - **Bookkeeping.** [Stage composition](p2m:theorem/4d8ff1cc-3ad3-4532-8242-676d24376e12) assembles the two pieces.
--
--   **Numeric budget** (checked in Python with exact integers). $U\log5/(6D^5)=3.74684244719\ldots$ against $3.7468424$, a slack of $4.7\cdot10^{-8}$ per $6D^5t$.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); WP6/WP7 of marwahaha's plan comment of 2026-09-24; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv 2404.16349 (Theorem 6.4 and Algorithm 1: the level-2 hash is pooled over all level-2 terms).

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
set_option autoImplicit false

theorem mme_released_level2_pooled_positive_recipe :
    ∃ C : ℕ, ∀ᶠ t : ℕ in atTop,
      ∃ R : LogJointRecipeG (lenAt RecStage.n2 t * 2 ^ (1 - 1)) 2 (fun i x ↦
          ParentGraded RecStage.parent2 (fun r ↦ t * RecStage.n2 r) i
            (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 t) rfl x) ∧
          parentTypical RecStage.htotal2 (fun r ↦ t * RecStage.n2 r)
            (fun r c ↦ t * RecStage.m2 r c) (fun c w ↦ t * RecStage.mu2 i c w)
            (Real.sqrt (8 * (25 * (1104 : ℝ) *
              (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
              ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
            (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 t) rfl x)),
        1 ≤ R.inputs ∧ R.inputs ≤ (t + 1) ^ C ∧ 1 ≤ R.a * R.b * R.c ∧
        ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) * t ≤ R.logOutputs ∧
        ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) * t ≤ Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  sorry
