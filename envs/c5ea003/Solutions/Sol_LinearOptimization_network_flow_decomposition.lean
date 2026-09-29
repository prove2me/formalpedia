-- Prove2me | solution 1 for LinearOptimization.network_flow_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T18:23:45.550025+00:00
-- url     : https://prove2.me/submissions/4dee94d4-d692-4be6-8d69-0536cc29399c

import Theorems.Thm_LinearOptimization_network_flow_decomposition_including_zero

open Matrix

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n)
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (f : Fin m → ℝ) (hnn : 0 ≤ f)
    (hcirc : LinearOptimization.IsCirculation arcs f)
    (_hne : f ≠ 0) :
    (∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℝ),
      (∀ i, ∃ v, LinearOptimization.IsCycle arcs v (cyc i)) ∧
      (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
      (∀ i, 0 < a i) ∧
      f = fun e => ∑ i, a i * LinearOptimization.traversalVector (cyc i) e) ∧
    ((∀ e, ∃ z : ℤ, f e = (z : ℝ)) →
      ∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℤ),
        (∀ i, ∃ v, LinearOptimization.IsCycle arcs v (cyc i)) ∧
        (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
        (∀ i, 0 < a i) ∧
        f = fun e => ∑ i, (a i : ℝ) *
          LinearOptimization.traversalVector (cyc i) e) := by
  exact LinearOptimization.network_flow_decomposition_including_zero
    arcs hloop f hnn hcirc
