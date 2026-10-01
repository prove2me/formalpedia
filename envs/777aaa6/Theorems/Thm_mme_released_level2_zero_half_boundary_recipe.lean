-- Prove2me | Theorems.Thm_mme_released_level2_zero_half_boundary_recipe
-- name    : mme_released_level2_zero_half_boundary_recipe
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:50:41.094443+00:00
-- url     : https://prove2.me/theorems/05939b6d-38ad-42f9-af3d-3b2f67f90537
-- title:
--   Exact boundary for the zero level-2 halves
-- statement:
--   This is the exact-profile boundary for the level-2 halves whose grade triple has a zero coordinate (WP6, "zero-half boundary"), with its dimension budget.
--
--   **Setting.** A **zero cell** is a pair $z=(\rho,c)$ where $\rho\in\mathrm{Fin}\,6$ is a level-3 region and $c=(r,s)\in\mathrm{Cell}(4,88,\texttt{parent3}\,\rho)$ is a level-3 cell whose half-grade triple $s$ has a zero coordinate. Its unit mass is
--   $$M(z)=m_3(\rho,r,s)+m_3(\rho,r,\bar s),$$
--   where $\bar s$ is the complementary split. Let $\sigma_\rho$ be `roleEquiv` $\rho$. Take any $L$ and any map $\zeta:\mathrm{Fin}\,L\to\{\text{zero cells}\}$ with fibres of size $|\zeta^{-1}(z)|=K\,M(z)$. Each $p<L$ is one level-2 half, made of two fine letters. The source $Z_{K,\zeta}$ holds in physical mode $i$ for a word $x$ on $2L$ letters when:
--   - every half $p$ has grade $s_{\zeta(p)}(\sigma_\rho^{-1}i)$;
--   - the joint histogram of half-words per zero cell is exactly $K\,\mu^{(3)}_{\rho}(\sigma_\rho^{-1}i)$ (`Useful`).
--
--   **Claim.** There is $C$ such that for all sufficiently large $K$, for all $L$ and $\zeta$ as above, there is a level-2 `LogJointRecipeG` $R$ with source $Z_{K,\zeta}$ satisfying
--   $$1\le\mathrm{inputs}(R)\le(K+1)^C,\quad 0\le\mathrm{logOutputs}(R),\quad 1\le abc,\quad 209101632051\cdot6\cdot10^{49}\,K\le\log(abc).$$
--
--   **Why it should hold.** This is an instance of the [exact-profile boundary end](p2m:theorem/2c6d3aa4-183c-4680-b806-283597581306) at $\ell=2$, applied as a `base` recipe. Take the zero mode to be $\sigma_\rho$ of a zero coordinate of $s$, and the count to be $K\mu^{(3)}$ in the next mode. The third mode is its `flipLabel`, by `BoundaryProfiles` of $\mu^{(3)}$, which holds for released frames. So
--   $$abc=\prod_z\binom{K M(z)}{K\mu^{(3)}(z,\cdot)}\,5^{\,K\sum_w\mu^{(3)}(z,w)\,\mathrm{ones}(w)} .$$
--   By the [multinomial mass-entropy lower bound](p2m:theorem/69879847-c4f7-4e58-96b4-b3ba44424367), $\log abc\ge K\beta_0\cdot 6D^5-O(\log K)$.
--
--   **Numeric budget.** Computed exactly from the released tables with 40-digit logs, the unit value is $\beta_0=2.09101637250\ldots$ per $6D^5$ against the target $2.09101632051$, a slack of $5.2\cdot10^{-8}$ per $6D^5K$. The $O(\log K)$ multinomial loss, over about $2.6\cdot10^3$ zero cells with $9$ words each, is eventually negligible.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); WP6/WP7 of marwahaha's plan comment of 2026-09-24; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv 2404.16349 (Theorem 6.4 and Algorithm 1: the level-2 hash is pooled over all level-2 terms).

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_released_level2_zero_half_boundary_recipe :
    ∃ C : ℕ, ∀ᶠ K : ℕ in atTop, ∀ (L : ℕ)
      (zc : Fin L → (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
        ∃ j, (c.2.val j).val = 0}),
      (∀ z, Fintype.card {p : Fin L // zc p = z} =
        K * (RecStage.m3 z.1 z.2.1.1 z.2.1.2 +
          RecStage.m3 z.1 z.2.1.1 (complement (RecStage.htotal3 z.1 z.2.1.1) z.2.1.2))) →
      ∃ R : LogJointRecipeG (L * 2 ^ (2 - 1)) 2 (fun i x ↦
          (∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x p) =
            ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
          Useful zc (fun z w ↦ K * RecStage.mu3 z.1
              ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
            (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl x)),
        1 ≤ R.inputs ∧ R.inputs ≤ (K + 1) ^ C ∧ 0 ≤ R.logOutputs ∧ 1 ≤ R.a * R.b * R.c ∧
        ((209101632051 * 6 * 10 ^ 49 : ℕ) : ℝ) * K ≤
          Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  sorry
