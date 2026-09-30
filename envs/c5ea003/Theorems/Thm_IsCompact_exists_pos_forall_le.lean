-- Prove2me | Theorems.Thm_IsCompact_exists_pos_forall_le
-- name    : IsCompact.exists_pos_forall_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T22:42:49.627981+00:00
-- url     : https://prove2.me/theorems/bc76e9a6-70f0-4341-af11-bce690919552
-- title:
--   Positive uniform lower bound on a compact set
-- statement:
--   Let $s$ be a nonempty compact set in a topological space and $f:s\to\mathbb{R}$ continuous and everywhere positive. Then there is $m>0$ with $m\le f(x)$ for all $x\in s$. Take a minimizer from compactness. Used for uniform arm-length bounds.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Topology/Order/Compact.lean#L5-L10

import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
open IsCompact

namespace IsCompact

theorem exists_pos_forall_le {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s) (hne : s.Nonempty) {f : X → ℝ} (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, 0 < f x) : ∃ m > 0, ∀ x ∈ s, m ≤ f x := by sorry

end IsCompact
