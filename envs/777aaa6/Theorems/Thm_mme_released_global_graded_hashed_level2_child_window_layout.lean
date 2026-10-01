-- Prove2me | Theorems.Thm_mme_released_global_graded_hashed_level2_child_window_layout
-- name    : mme_released_global_graded_hashed_level2_child_window_layout
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:54:06.04777+00:00
-- url     : https://prove2.me/theorems/997ca8c6-9b5a-4c4c-aa7d-ba17775d61bb
-- title:
--   Layout from child windows to pooled level-2 and zero-half sources
-- statement:
--   This is the position layout that links the six regional child windows of the level-3 stage to the pooled level-2 source and the zero-half boundary source. It is the "source compatible with `childWindow`" part of WP6.
--
--   **Setting.** This uses the notation of [the level-2 continuation from child windows](p2m:theorem/fe68374b-2f02-46f9-904e-d0b4b4de5d83). The window predicate $\mathcal W_\delta(i,y)$ says: for every region $r$, the word $y_r=y\circ E(r,\cdot)$ read through frame $F_r$ is graded in mode $\sigma_r^{-1}i$, and every level-3 cell's half-word frequency is within $\delta$ of that of $k^2\mu^{(3)}_r(\sigma_r^{-1}i)$. Two further sources are used:
--   - $S_t$ is the pooled level-2 source of [the pooled level-2 step](p2m:theorem/089fbb5d-a337-4731-9e66-0514247f1174) (parent-graded and `parentTypical` at tolerance $\tau_t$) at $t=k^2$;
--   - $Z_{K,\zeta}$ is the zero-half source of [the zero-half boundary](p2m:theorem/05939b6d-38ad-42f9-af3d-3b2f67f90537) at $K=k^2$.
--
--   **Claim.** For every $\delta>0$ and all sufficiently large $k$ there are:
--   - a reference family $a$ and released frames $F_r$ at scale $k^2$ such that, for **every** bijection $E$;
--   - $L$ and $\zeta:\mathrm{Fin}\,L\to\{\text{zero cells}\}$ with fibres $k^2M(z)$;
--   - a bijection $\mathrm{pos}:\mathrm{Fin}(\mathrm{len}_{k^2})\sqcup\mathrm{Fin}(2L)\simeq\mathrm{Fin}\,N_{k^2}(a)$;
--
--   such that for all $i$ and $y$,
--   $$S_{k^2}(i,\ y\circ\mathrm{pos}\circ\mathrm{inl})\ \wedge\ Z_{k^2,\zeta}(i,\ y\circ\mathrm{pos}\circ\mathrm{inr})\ \Longrightarrow\ \mathcal W_\delta(i,y).$$
--
--   **Why it should hold.** Each level-3 half of region $\rho$ lies in the cell $\mathrm{fullCell}(F_\rho.\mathrm{ref},p)=(r,s)$.
--   - **Zero halves.** Halves with a zero in $s$ go to $\zeta$ with $\zeta=(\rho,(r,s))$. Since $F_\rho.\mathrm{ref}$ lies in the target, the fibre sizes are $k^2M(z)$.
--   - **Positive halves.** Halves with $s$ positive go to the level-2 region matching $(\rho,r,s)$, whose two fine letters are that block's two level-1 halves. There is an exact bijection between the $1104$ positive cells $(\rho,r,s)$ and the $1104$ level-2 terms, checked in Python on the released tables:
--     - the shape is $s\circ\sigma_\rho^{-1}$ (physical orientation);
--     - the weight is $w_3(\rho,r)\,(\mathrm{wt}_s+\mathrm{wt}_{\bar s})$;
--     - the split parameter is $s_0$ of the cell.
--
--     So the block counts agree, $k^2M=k^2n_2$.
--   - **Mixtures.** The level-2 mixture equals the cell's word frequency: both are $\texttt{childW}(\cdot)/D$, and `jw` is symmetric under permuting coordinates.
--   - **Conclusion.** Parent-gradedness gives the level-3 grades. $\tau_{k^2}\to0$ gives the $\delta$-windows on positive cells. Exact zero-cell histograms give frequency error $0$. Cells with no halves have frequency $0$ on both sides.
-- source:
--   Prove2Me mission 7e65274f (More Asymmetry Bound: omega < 2.37134); WP6/WP7 of marwahaha's plan comment of 2026-09-24; released data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv 2404.16349 (Theorem 6.4 and Algorithm 1: the level-2 hash is pooled over all level-2 terms). Level-3 frames: mme_released_positive_integer_frame (8aa8d8f3).

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
import Definitions.Def_mme_regional_tolerance_window_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm MME.DWZProfiledRegional
open scoped Classical
set_option autoImplicit false

theorem mme_released_global_graded_hashed_level2_child_window_layout :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in atTop,
      ∃ (a : ∀ o : Fin 6, Reference o (k^2))
        (frame : ∀ r : Fin 6, ReleasedPositiveInteger.Frame r (k^2)),
      ∀ E : ((r : Fin 6) × Fin (ReleasedJointInterior.blocks r (k^2) * 4)) ≃
          Fin (partSize (k^2) a 1),
      ∃ (L : ℕ) (zc : Fin L → (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
          ∃ j, (c.2.val j).val = 0}),
        (∀ z, Fintype.card {p : Fin L // zc p = z} =
          k^2 * (RecStage.m3 z.1 z.2.1.1 z.2.1.2 +
            RecStage.m3 z.1 z.2.1.1 (complement (RecStage.htotal3 z.1 z.2.1.1) z.2.1.2))) ∧
        ∃ pos : (Fin (lenAt RecStage.n2 (k^2) * 2 ^ (1 - 1)) ⊕ Fin (L * 2 ^ (2 - 1))) ≃
            Fin (partSize (k^2) a 1),
          ∀ (i : Fin 3) (y : FineWord (partSize (k^2) a 1)),
            (ParentGraded RecStage.parent2 (fun r ↦ k^2 * RecStage.n2 r) i
                (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 (k^2)) rfl
                  (fun q ↦ y (pos (Sum.inl q)))) ∧
              parentTypical RecStage.htotal2 (fun r ↦ k^2 * RecStage.n2 r)
                (fun r c ↦ k^2 * RecStage.m2 r c) (fun c w ↦ k^2 * RecStage.mu2 i c w)
                (Real.sqrt (8 * (25 * (1104 : ℝ) *
                  (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
                  ((Nat.sqrt (k^2) + 2 : ℕ) : ℝ) / (k^2 : ℕ)))
                (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 (k^2)) rfl
                  (fun q ↦ y (pos (Sum.inl q))))) →
            ((∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                  (fun q ↦ y (pos (Sum.inr q))) p) =
                ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
              Useful zc (fun z w ↦ k^2 * RecStage.mu3 z.1
                  ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
                (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                  (fun q ↦ y (pos (Sum.inr q))))) →
            ∀ r : Fin 6,
              RecursiveYZ.Graded (RecStage.htotal3 r) ((ReleasedJointInterior.roleEquiv r).symm i)
                (frame r).reference
                (ProfiledCW.split (ell := 2) (frame r).positions
                  (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩))) ∧
              ∀ c w, |cellFrequency (RecursiveYZ.count (fullCell (RecStage.htotal3 r) (frame r).reference)
                  (ProfiledCW.split (ell := 2) (frame r).positions
                    (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩)))) c w -
                cellFrequency (fun c w ↦ k^2 * RecStage.mu3 r ((ReleasedJointInterior.roleEquiv r).symm i) c w) c w| ≤ δ := by
  sorry
