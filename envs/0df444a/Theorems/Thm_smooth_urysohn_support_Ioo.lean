-- Prove2me | Theorems.Thm_smooth_urysohn_support_Ioo
-- name    : smooth_urysohn_support_Ioo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:01.179895+00:00
-- url     : https://prove2.me/theorems/36746d0a-bb64-4b3d-a2c4-ce737ecb18bb
-- title:
--   smooth urysohn support Ioo: smooth urysohn support Ioo
-- statement:
--   The smooth urysohn support Ioo construction uses the smooth urysohn support Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L12-L44
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L12-L44

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
set_option autoImplicit true
open MeasureTheory Set Real
open scoped ContDiff Manifold

theorem smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by sorry
