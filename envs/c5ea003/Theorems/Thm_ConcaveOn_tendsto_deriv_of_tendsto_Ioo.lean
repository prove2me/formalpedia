-- Prove2me | Theorems.Thm_ConcaveOn_tendsto_deriv_of_tendsto_Ioo
-- name    : ConcaveOn.tendsto_deriv_of_tendsto_Ioo
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T03:02:11.41067+00:00
-- url     : https://prove2.me/theorems/6e85f73b-3128-4d34-b429-d162b903e93b
-- title:
--   Derivatives converge under pointwise convergence
-- statement:
--   Pointwise convergence of concave functions forces derivative convergence at a common interior differentiability point, via slope order limits.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Convex/Deriv.lean#L34-L68

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
open Filter Set
open scoped Topology

namespace ConcaveOn

theorem tendsto_deriv_of_tendsto_Ioo {ι : Type*} {F : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hf : Filter.Eventually (fun n => ConcaveOn ℝ (Ioo a b) (f n)) F)
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun n ↦ f n y) F (nhds (g y)))
    (hdf : Filter.Eventually (fun n => DifferentiableAt ℝ (f n) x) F)
    (hdg : DifferentiableAt ℝ g x) :
    Tendsto (fun n ↦ deriv (f n) x) F (nhds (deriv g x)) := by sorry

end ConcaveOn
