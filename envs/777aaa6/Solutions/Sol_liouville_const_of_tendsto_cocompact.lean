-- Prove2me | solution 1 for liouville_const_of_tendsto_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:39:44.989559+00:00
-- url     : https://prove2.me/submissions/8060493e-23e7-4fc5-a7fe-3d8a89ef8772

import Mathlib.Analysis.Complex.Liouville

open Filter Topology

theorem solution {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ}
    (hgc : Tendsto g (cocompact ℂ) (𝓝 c)) (z : ℂ) : g z = c := by
  exact hg.apply_eq_of_tendsto_cocompact z hgc
