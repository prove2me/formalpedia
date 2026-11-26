-- Prove2me | Theorems.Thm_exists_bounded_simpleFunc_tendstoUniformly
-- name    : exists_bounded_simpleFunc_tendstoUniformly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:41.136828+00:00
-- url     : https://prove2.me/theorems/26a7a0dd-ad9e-4f04-8fa1-9f68f4bb1e81
-- title:
--   exists bounded simple Func tendsto Uniformly: exists bounded simple Func tendsto Uniformly
-- statement:
--   A bounded measurable complex-valued function admits uniformly convergent simple
--   approximations obeying the same pointwise norm bound.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L416-L423
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L416-L423

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_bounded_simpleFunc_tendstoUniformly (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc ℝ ℂ,
      TendstoUniformly (fun n t => s n t) f Filter.atTop ∧
        ∀ n t, ‖s n t‖ ≤ C := by sorry
