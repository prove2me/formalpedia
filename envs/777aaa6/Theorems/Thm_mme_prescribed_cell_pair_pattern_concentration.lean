-- Prove2me | Theorems.Thm_mme_prescribed_cell_pair_pattern_concentration
-- name    : mme_prescribed_cell_pair_pattern_concentration
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T17:09:01.499142+00:00
-- url     : https://prove2.me/theorems/ff93bdeb-2c4a-4a81-8be9-7cda58205fdb
-- title:
--   Concentration of actual paired words under exact cell histograms
-- statement:
--   For disjoint pairs of queried positions in a nonempty exact cell-histogram word class, the frequency of any fixed pair-word is within epsilon of its product-mixture average except on a fraction at most 25/(m epsilon squared). Assumptions are only finite histogram data, disjoint positions and minimum cell/occurrence sizes. No first- or second-moment bounds are assumed.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Theorems.Thm_mme_prescribed_cell_sampling_pattern_approximation
import Theorems.Thm_mme_finite_pair_moment_concentration

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem mme_prescribed_cell_pair_pattern_concentration {P C W T : Type*} [Fintype P] [Fintype W] [Fintype T]
    (cell : P → C) (mu : C → W → ℕ) (q : T × Fin 2 → P) (hq : Function.Injective q)
    (w : Fin 2 → W) (hU : Nonempty {f : P → W // Useful cell mu f})
    (m : ℕ) (hm : 0 < m) (hmn : m ≤ Fintype.card T)
    (hsize : ∀ t h, m ≤ Fintype.card {p : P // cell p = cell (q (t,h))})
    (eps : ℝ) (heps : 0 < eps) :
    (𝔼 f : {f : P → W // Useful cell mu f},
      if eps ≤ |((∑ t : T, if (∀ h : Fin 2, f.val (q (t,h)) = w h) then (1 : ℝ) else 0) -
        ∑ t : T, ∏ h : Fin 2, ((mu (cell (q (t,h))) (w h) : ℝ) /
          Fintype.card {p : P // cell p = cell (q (t,h))})) / Fintype.card T|
      then (1 : ℝ) else 0) ≤ 25 / ((m : ℝ) * eps ^ 2) := by sorry
