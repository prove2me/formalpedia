-- Prove2me | Theorems.Thm_mme_released_level2_level3_positive_cell_correspondence
-- name    : mme_released_level2_level3_positive_cell_correspondence
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:04:35.337988+00:00
-- url     : https://prove2.me/theorems/f7585a6e-a1ca-466e-80c3-aa7731d0e97e
-- title:
--   Level-2 terms match the positive level-3 cells
-- statement:
--   This is the finite data correspondence between the positive level-3 cells of the six released regions and the $1104$ pooled level-2 terms (`RecStage` tables). It is the data half of the [child-window layout](p2m:theorem/997ca8c6-9b5a-4c4c-aa7d-ba17775d61bb).
--
--   **Setting.** Let $D=10^{12}$. A level-3 cell is a pair $(\rho,c)$: $\rho\in\mathrm{Fin}\,6$ is a region, and $c=(r,s)$ has parent $r<88$ and a half-grade triple $s$ with $s_0+s_1+s_2=4$ and $s\le\texttt{parent3}(\rho,r)$. Write $\bar s$ for the complementary split and
--   $$M(\rho,c)=m_3(\rho,r,s)+m_3(\rho,r,\bar s)$$
--   for its unit mass. The cell is **positive** if $s_0,s_1,s_2\neq0$. Let $\sigma_\rho$ be `roleEquiv` $\rho$.
--
--   **Claim.** There is a map $\varphi:\mathrm{Fin}\,1104\to\{\text{level-3 cells}\}$ such that:
--   1. $\varphi$ is injective, and every $\varphi(r)$ is positive;
--   2. every positive cell with $M>0$ is in the image of $\varphi$;
--   3. $n_2(r)=M(\varphi(r))$;
--   4. $\texttt{parent2}(r)(i)=s_{\varphi(r)}(\sigma_{\rho}^{-1}i)$, where $\rho$ is the region of $\varphi(r)$ (the physical orientation);
--   5. for every mode $i$ and every two-letter word $w=(w_0,w_1)$, the level-2 parent mixture equals the level-3 cell frequency:
--   $$\mathrm{parentMixture}(n_2,m_2,\mu_2(i))\big(r,(w_0),(w_1)\big)=\frac{\mu^{(3)}_{\rho}(\sigma_\rho^{-1}i)(\varphi(r),w)}{\sum_v\mu^{(3)}_{\rho}(\sigma_\rho^{-1}i)(\varphi(r),v)} .$$
--
--   **Why it holds.** Take $\varphi(r)$ to be the unique positive level-3 cell $(\rho,r_3,s)$ whose key
--   $$\big(s\circ\sigma_\rho^{-1},\ w_3(\rho,r_3)\,(\mathrm{wt}_s+\mathrm{wt}_{\bar s}),\ s_0(\rho,r_3,s)\big)$$
--   equals the table entry `l2At r`. All keys are distinct, and the two multisets of keys coincide. For item 5, both sides equal $\sum_{e}\,jw(a,s_0,e)/D$ over the level-1 splits $e$ with $e_{i'}=w_0$ and $(a-e)_{i'}=w_1$, because `jw` is symmetric under permuting coordinates and $\sum_w \texttt{childW}=D$ on cells with positive mass. All five items were checked in Python with exact rational arithmetic, following the Lean definitions (`cellRec` via `find?`, integer division in `mu3`).
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv 2404.16349 (Algorithm 1, level-2 terms). Data half of mme_released_global_graded_hashed_level2_child_window_layout (997ca8c6).

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Definitions.Def_mme_recursive_region_parent_profiles
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_released_level2_level3_positive_cell_correspondence :
    ∃ φ : Fin 1104 → (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ),
      Function.Injective φ ∧
      (∀ r j, ((φ r).2.2.val j).val ≠ 0) ∧
      (∀ (ρ : Fin 6) (c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ)),
        (∀ j, (c.2.val j).val ≠ 0) →
        0 < RecStage.m3 ρ c.1 c.2 + RecStage.m3 ρ c.1 (complement (RecStage.htotal3 ρ c.1) c.2) →
        ∃ r, φ r = ⟨ρ, c⟩) ∧
      (∀ r, RecStage.n2 r = RecStage.m3 (φ r).1 (φ r).2.1 (φ r).2.2 +
        RecStage.m3 (φ r).1 (φ r).2.1 (complement (RecStage.htotal3 (φ r).1 (φ r).2.1) (φ r).2.2)) ∧
      (∀ r i, RecStage.parent2 r i =
        ((φ r).2.2.val ((ReleasedJointInterior.roleEquiv (φ r).1).symm i)).val) ∧
      (∀ r i (w : CompleteSplit.CompleteWord 2),
        parentMixture RecStage.htotal2 RecStage.n2 RecStage.m2 (RecStage.mu2 i) r
            (fun h _ ↦ w h) =
          cellFrequency (RecStage.mu3 (φ r).1 ((ReleasedJointInterior.roleEquiv (φ r).1).symm i))
            (φ r).2 w) := by
  sorry
