-- Prove2me | solution 1 for Bishop.Reg.toReal_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:44:18.185796+00:00
-- url     : https://prove2.me/submissions/a39f2b20-559e-482a-8673-1b92e931b656

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
open Bishop Bishop.Reg Filter Topology in
theorem solution (x y : Reg) : (add x y).toReal = x.toReal + y.toReal := by
  -- `add` samples both arguments along `n ↦ 2n+1`, a subsequence tending to `atTop`
  have hidx : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hx : Filter.Tendsto (fun n : ℕ => ((x.approx (2 * n + 1) : ℚ) : ℝ)) Filter.atTop
      (nhds x.toReal) := (Bishop.Reg.tendsto_toReal x).comp hidx
  have hy : Filter.Tendsto (fun n : ℕ => ((y.approx (2 * n + 1) : ℚ) : ℝ)) Filter.atTop
      (nhds y.toReal) := (Bishop.Reg.tendsto_toReal y).comp hidx
  have hap : ∀ n : ℕ, (((add x y).approx n : ℚ) : ℝ)
      = ((x.approx (2 * n + 1) : ℚ) : ℝ) + ((y.approx (2 * n + 1) : ℚ) : ℝ) := by
    intro n
    show (((x.approx (2 * n + 1) + y.approx (2 * n + 1) : ℚ)) : ℝ) = _
    push_cast
    ring
  show Filter.limUnder Filter.atTop (fun n : ℕ => (((add x y).approx n : ℚ) : ℝ))
      = x.toReal + y.toReal
  have hsum : Filter.Tendsto (fun n : ℕ => (((add x y).approx n : ℚ) : ℝ)) Filter.atTop
      (nhds (x.toReal + y.toReal)) := by
    have := hx.add hy
    exact this.congr fun n => (hap n).symm
  exact hsum.limUnder_eq
