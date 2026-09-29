-- Prove2me | solution 1 for sign_transfer_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T18:23:19.892062+00:00
-- url     : https://prove2.me/submissions/a787b9f1-e3e4-4fd2-9b4f-3dc1067b0a3d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

/-- **Siegel 2001, Thm 2.1/2.2 — sign-transfer from log-density to density difference.** -/
theorem solution
    (f : ℝ → ℝ) (μ c : ℝ)
    (hf : ∀ x, 0 < f x)
    (hL : ∀ x ∈ Icc (0:ℝ) c, Real.log (f x) - Real.log (f (2*μ - x)) ≤ 0)
    (hR : ∀ x ∈ Icc c μ, 0 ≤ Real.log (f x) - Real.log (f (2*μ - x))) :
    (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0) ∧
    (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) := by
  constructor
  · intro x hx
    have h := hL x hx
    have hlog : Real.log (f x) ≤ Real.log (f (2*μ - x)) := by linarith
    have hle : f x ≤ f (2*μ - x) := (Real.log_le_log_iff (hf x) (hf (2*μ-x))).mp hlog
    linarith
  · intro x hx
    have h := hR x hx
    have hlog : Real.log (f (2*μ - x)) ≤ Real.log (f x) := by linarith
    have hle : f (2*μ - x) ≤ f x := (Real.log_le_log_iff (hf (2*μ-x)) (hf x)).mp hlog
    linarith
