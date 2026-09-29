-- Prove2me | solution 1 for lean_workbook_plus_75383
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:56:58.583196+00:00
-- url     : https://prove2.me/submissions/fcd9858b-8ef3-4c72-b876-f024ee94a0a0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∃ c : ℤ, ∀ d : ℤ, ∃ x y z t : ℤ, x^3 + y^3 + z^3 + t^3 = 1999 ∧ x > d ∧ y > d ∧ z > d ∧ t > d) := by
  have hbnd : ∀ v : ℤ, 10 < v → 1000 ≤ v^3 := by
    intro v hv
    have hv0 : 0 ≤ v := by omega
    have hp := mul_nonneg (show 0 ≤ v-10 by omega) (show 0 ≤ v^2+10*v+100 by positivity)
    nlinarith only [hp]
  intro h
  rcases h with ⟨c,hc⟩
  rcases hc 10 with ⟨x,y,z,t,he,hx,hy,hz,ht⟩
  have hxb := hbnd x hx
  have hyb := hbnd y hy
  have hzb := hbnd z hz
  have htb := hbnd t ht
  linarith only [he,hxb,hyb,hzb,htb]
