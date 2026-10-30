-- Prove2me | Theorems.Thm_continuous_log_ratio_of_complement_component
-- name    : continuous_log_ratio_of_complement_component
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:04:20.196922+00:00
-- url     : https://prove2.me/theorems/68a5cc25-3b31-4b96-9119-ff69e870f36c
-- title:
--   A logarithm from a path in the complement of a closed set
-- statement:
--   Let $K$ be a closed subset of the complex plane, and let $a,b$ lie in the same connected component of $\mathbb C\setminus K$. Then the function
--
--   $$z\longmapsto\frac{z-a}{z-b}$$
--
--   has a continuous complex logarithm on $K$: there is a function $f$, continuous on $K$, whose exponential equals the displayed ratio at every point of $K$. This is one direction of a logarithmic characterization relevant to planar separation.
-- source:
--   Derived from the covering-space homotopy lifting theorem, Mathlib.Topology.Homotopy.Lifting, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Homotopy/Lifting.lean ; related to the homotopy characterization used in Isabelle/HOL Jordan_Curve, Janiszewski_weak, https://isabelle.in.tum.de/website-Isabelle2017/dist/library/HOL/HOL-Analysis/Jordan_Curve.html

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

open Set Function Topology unitInterval

theorem continuous_log_ratio_of_complement_component
    (K : Set ℂ) (hK : IsClosed K) (a b : ℂ)
    (hab : b ∈ connectedComponentIn Kᶜ a) :
    ∃ f : ℂ → ℂ, ContinuousOn f K ∧
      EqOn (fun z => Complex.exp (f z)) (fun z => (z - a) / (z - b)) K := by sorry
