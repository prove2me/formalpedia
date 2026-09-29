-- Prove2me | solution 1 for UltrametricRateDistortion.ultraBall_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:51:06.83098+00:00
-- url     : https://prove2.me/submissions/f4f8b5cc-78ed-4bf5-8161-4843fad9c4b7

import Mathlib
import Definitions.Def_Bridges_UltrametricProofRateDistortion
open UltrametricRateDistortion in
theorem solution {P : Type*} {d : P → P → ℝ} (hU : UltrametricDist d) {x y : P} {ε : ℝ}
    (hxy : y ∈ ultraBall d x ε) : ultraBall d x ε = ultraBall d y ε := by
  obtain ⟨-, -, hsymm, htri⟩ := hU
  have hxy' : d x y ≤ ε := hxy
  -- every point of an ultrametric ball is a centre
  ext z
  show d x z ≤ ε ↔ d y z ≤ ε
  constructor
  · intro hz
    calc d y z ≤ max (d y x) (d x z) := htri y x z
      _ ≤ ε := max_le (by rw [hsymm]; exact hxy') hz
  · intro hz
    calc d x z ≤ max (d x y) (d y z) := htri x y z
      _ ≤ ε := max_le hxy' hz
