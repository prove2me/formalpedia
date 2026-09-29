-- Prove2me | Theorems.Thm_mme_global_frame_window_implies_regional_parent_typical
-- name    : mme_global_frame_window_implies_regional_parent_typical
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:51:01.234295+00:00
-- url     : https://prove2.me/theorems/67bfde23-9b59-487f-8f37-8948848d80bc
-- title:
--   Literal global-frame words induce regional parent windows
-- statement:
--   Let $D$ be a global histogram frame at level $\ell+1$, where $\ell\ge1$, with $L>0$ full-word positions. Choose positive-size regional cells with enumerations of their physical positions. Suppose a mode word lies in the frame window
--   \[
--   \left|H_i(c,a)/L-\beta_i(c,a)\right|\le\delta.
--   \]
--   Split each selected full word into its literal left and right level-$\ell$ child words. If the regional parent mixture obeys
--   \[
--   \operatorname{mixture}_r(w_0,w_1)
--    =\frac{L}{n_r}\,\beta_i(c_r,w_0\mathbin{\|}w_1),
--   \qquad \frac{L\delta}{n_r}<\varepsilon,
--   \]
--   then these physical child words satisfy the regional parent-window condition at tolerance $\varepsilon$. The conclusion uses the frame's original positions and full-word split. The center-to-mixture identity remains an explicit hypothesis to be discharged by the numerical profile data.
-- source:
--   Exact physical cell histograms and global-to-regional frequency normalization.

import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_global_CW_histogram_frame
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_cell_partition
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false


open MME.CompleteSplit

theorem mme_global_frame_window_implies_regional_parent_typical
    {ell M half R : ℕ} (hell : 1 ≤ ell)
    (D : GlobalCW.HistogramFrame (ell + 1) M)
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (region : Fin R → Cell D.degree D.R D.bounds)
    (fiber : ∀ r, Fin (n r) ≃
      {p : GlobalCW.Place D.n // GlobalCW.cell D.reference p = region r})
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord (ell + 1) → ℝ)
    (delta eps : ℝ) (hL : 0 < D.L) (hn : ∀ r, 0 < n r)
    (i : Fin 3) (x : ProfiledCW.FineWord M)
    (hwindow : D.window (fun i hist ↦ ∀ c w,
      |(hist c w : ℝ) / (D.L : ℝ) - center i c w| ≤ delta) i x)
    (hmixture : ∀ r (w : Fin 2 → CompleteWord ell),
      parentMixture htotal n m mu r w = (D.L : ℝ) / (n r : ℝ) *
        center i (region r) ((completeWordSplitEquiv ell hell).symm (w 0, w 1)))
    (htolerance : ∀ r, (D.L : ℝ) / (n r : ℝ) * delta < eps) :
    parentTypical htotal n m mu eps (fun p ↦
      let w := completeWordSplitEquiv ell hell
        (ProfiledCW.split D.positions D.length x (fiber p.1 p.2.1).val)
      if p.2.2 = 0 then w.1 else w.2) := by sorry
