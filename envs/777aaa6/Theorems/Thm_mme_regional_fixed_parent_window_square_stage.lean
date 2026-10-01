-- Prove2me | Theorems.Thm_mme_regional_fixed_parent_window_square_stage
-- name    : mme_regional_fixed_parent_window_square_stage
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T20:01:48.645972+00:00
-- url     : https://prove2.me/theorems/0c054ab2-3215-4bdd-a6ae-2edf3d3dc503
-- title:
--   Square-scale recursive stages with a fixed parent-window center
-- statement:
--   Fix a recursive level $\ell$, positive integer regional sizes $n_r$, nonnegative integer split counts $m_{r,s}$ summing to $n_r$, and integer child histograms $\mu_{i,s,w}$ with the prescribed cell masses $m_{r,s}+m_{r,\bar s}$. Let $\rho\ge0$ be strictly below their regional extraction rate. Fix $\varepsilon>0$ and a parent-pair distribution $\beta_{i,r}$ equal to the central mixture of the two child-cell distributions.
--
--   There are $\delta>0$ and $k_0$ such that, for every integer $k\ge k_0$ and every address realizing the split counts $k^2m$, there is an actual graded part stage with:
--
--   * source: parent-graded words whose regional pair frequencies are within $\varepsilon$ of the fixed center $\beta$;
--   * target: address-graded words whose child histograms have exactly the cell masses of $k^2\mu$, with each count within $\delta$ times that cell mass of $k^2\mu$;
--   * rate exactly $\rho k^2$;
--   * at most $(k+1)^{9|\mathrm{Cell}|\,|W_\ell|}$ histogram types.
--
--   The tolerance and scale threshold are uniform in the address and histogram types. The parent-window inclusion is proved from the center identity and a $2\delta$ Lipschitz bound. No separate source-inclusion hypothesis is required. At $\ell=3$, the words on the source side are the paired level-three children of a level-four parent.
--
--   The stage covers all supported target triples. A supported target triple is still required to ensure a positive type count. This auxiliary theorem does not assert existence of AlphaEvolve's numerical witness or its strict surplus.
-- source:
--   Generic auxiliary consequence of the Prove2Me graded band part-stage theorem (https://prove2.me/theorems/5d673b53-781e-4970-a100-af61d306eba4), parent-mixture Lipschitz theorem (https://prove2.me/theorems/7fadf806-0aa6-4a1e-bea2-3dcf357932b4), and replication theorem (https://prove2.me/theorems/e8de6d35-cf75-4236-a8eb-3262bf5543bd). Application context: recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, Sections 5-6, https://arxiv.org/abs/2404.16349; level-four application in Dupont et al., Section 2 and Section 4, https://arxiv.org/html/2608.16884v1. This uniform fixed-center square-scale statement is derived here, not quoted verbatim from either paper.

import Theorems.Thm_mme_graded_band_part_stage
import Theorems.Thm_mme_regional_parent_mixture_lipschitz
import Theorems.Thm_mme_parent_mixture_scale

open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization
  MME.DWZProfiledRegional
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem mme_regional_fixed_parent_window_square_stage {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ s, m r s = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i s, ∑ w, mu i s w = m s.1 s.2 + m s.1 (complement (htotal s.1) s.2))
    (rate eps : ℝ) (hr0 : 0 ≤ rate) (hr : rate < regionalRate htotal n m mu)
    (heps : 0 < eps)
    (center : Fin 3 → Fin R → (Fin 2 → CompleteSplit.CompleteWord ell) → ℝ)
    (hcenter : ∀ i r w, center i r w = parentMixture htotal n m (mu i) r w) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      0 < k ∧ ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ k ^ 2 * n r),
      a ∈ RecursiveXHash.target (n := fun r ↦ k ^ 2 * n r) (fun r s ↦ k ^ 2 * m r s) →
      ∃ D : LogPartStageG (lenAt n (k ^ 2) * 2 ^ (ell - 1)) ell
        (fun i x ↦
          let f := ProfiledCW.split (positionsAt n (k ^ 2)) rfl x
          ParentGraded parent (fun r ↦ k ^ 2 * n r) i f ∧
          ∀ r w, |(Fintype.card {t : Fin (k ^ 2 * n r) // ∀ h, f ⟨r,t,h⟩ = w h} : ℝ) /
            (k ^ 2 * n r : ℕ) - center i r w| < eps)
        (fun i y ↦
          let f := ProfiledCW.split (positionsAt n (k ^ 2)) rfl y
          let hist := count (fullCell htotal a) f
          Graded htotal i a f ∧
          (∀ s, ∑ w, hist s w = ∑ w, k ^ 2 * mu i s w) ∧
          ∀ s w, |(hist s w : ℝ) - ((k ^ 2 * mu i s w : ℕ) : ℝ)| ≤
            delta * ((∑ z, k ^ 2 * mu i s z : ℕ) : ℝ)),
        D.types ≤ (k + 1) ^
          (9 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
            Fintype.card (CompleteSplit.CompleteWord ell)) ∧ D.rate = rate * k ^ 2 := by sorry
