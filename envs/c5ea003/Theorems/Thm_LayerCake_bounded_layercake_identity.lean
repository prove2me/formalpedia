-- Prove2me | Theorems.Thm_LayerCake_bounded_layercake_identity
-- name    : LayerCake.bounded_layercake_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:59:20.178266+00:00
-- url     : https://prove2.me/theorems/6e075406-57f2-45af-84e6-f0ccc1ee837c
-- title:
--   Layer-cake identity on $[-M,M]$
-- statement:
--   Layer-cake representation of a bounded real.
--
--   If $|u|\le M$, then $u+M$ is the length of $[-M,u)$, i.e.
--
--   $$
--   u+M=\int_{-M}^M\mathbf 1_{\{u>t\}}\,dt.
--   $$
--
--   Indeed $[-M,M]\cap\{u>t\}=[-M,u)$ and the integral of $1$ is volume.
--
--   **Formalization Note** Integrals are set integrals against `volume`; indicators use `Set.indicator`.
-- source:
--   Standard layer-cake / Cavalieri; cf. Mathlib Layercake.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped Topology ENNReal

theorem LayerCake.bounded_layercake_identity (u M : ℝ) (h : |u| ≤ M) : u + M = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio u) 1 t := by sorry
