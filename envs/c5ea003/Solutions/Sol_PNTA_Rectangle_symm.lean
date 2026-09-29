-- Prove2me | solution 1 for PNTA.Rectangle.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T05:45:22.688802+00:00
-- url     : https://prove2.me/submissions/ba26daf5-9cf3-4274-9464-942718e76c8e

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone

open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}

theorem solution : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]
