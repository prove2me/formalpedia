-- Prove2me | solution 1 for LeblRA.algebra_closure
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:13:50.529184+00:00
-- url     : https://prove2.me/submissions/4c02fb58-068d-4fa1-902e-38122aa27b64

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA

theorem _root_.solution {X : Type*} [MetricSpace X] [CompactSpace X] :
    (∀ A : NonUnitalSubalgebra ℝ C(X, ℝ),
      ∃ B : NonUnitalSubalgebra ℝ C(X, ℝ), (B : Set C(X, ℝ)) = closure (A : Set C(X, ℝ))) ∧
    (∀ A : NonUnitalSubalgebra ℂ C(X, ℂ),
      ∃ B : NonUnitalSubalgebra ℂ C(X, ℂ), (B : Set C(X, ℂ)) = closure (A : Set C(X, ℂ))) := by
  exact ⟨fun A => ⟨A.topologicalClosure, rfl⟩, fun A => ⟨A.topologicalClosure, rfl⟩⟩

end LeblRA
