-- Prove2me | solution 1 for rectangle_mem_nhds_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:30:05.503399+00:00
-- url     : https://prove2.me/submissions/59d17d34-2c35-4e41-82da-0f2b7d4a2a3c

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem solution {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

