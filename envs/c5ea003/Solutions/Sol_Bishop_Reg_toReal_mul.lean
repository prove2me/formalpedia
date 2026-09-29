-- Prove2me | solution 1 for Bishop.Reg.toReal_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:27:16.103125+00:00
-- url     : https://prove2.me/submissions/34476dca-6e13-4b8f-ba27-e59dc0ae675d

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
open Bishop in
theorem solution (x y : Bishop.Reg) :
    (Bishop.Reg.mul x y).toReal = x.toReal * y.toReal := by
  have hshift : ∀ (z : Bishop.Reg) (f : ℕ → ℕ), (∀ n, n ≤ f n) →
      Filter.Tendsto (fun n => ((z.approx (f n) : ℚ) : ℝ)) Filter.atTop (nhds z.toReal) := by
    intro z f hf
    exact (Bishop.Reg.tendsto_toReal z).comp (Filter.tendsto_atTop_mono hf Filter.tendsto_id)
  have hidx : ∀ n : ℕ, n ≤ Bishop.Reg.mulIdx x y n := by
    intro n
    have hb : 1 ≤ x.bound + y.bound := le_trans x.one_le_bound (Nat.le_add_right _ _)
    unfold Bishop.Reg.mulIdx
    calc n ≤ n + 1 := by omega
      _ = 1 * (n + 1) := by ring
      _ ≤ (x.bound + y.bound) * (n + 1) := Nat.mul_le_mul_right _ hb
  have h1 := hshift x (Bishop.Reg.mulIdx x y) hidx
  have h2 := hshift y (Bishop.Reg.mulIdx x y) hidx
  have hprod : Filter.Tendsto (fun n => (((Bishop.Reg.mul x y).approx n : ℚ) : ℝ))
      Filter.atTop (nhds (x.toReal * y.toReal)) := by
    have hmul := h1.mul h2
    simpa [Bishop.Reg.mul] using hmul
  exact hprod.limUnder_eq
