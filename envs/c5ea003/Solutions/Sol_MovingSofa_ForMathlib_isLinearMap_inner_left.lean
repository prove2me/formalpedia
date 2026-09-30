-- Prove2me | solution 1 for MovingSofa.ForMathlib.isLinearMap_inner_left
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T21:49:08.690515+00:00
-- url     : https://prove2.me/submissions/faf4b372-0444-415a-b693-c06f4b0b56a3

import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : IsLinearMap ℝ fun x : E ↦ inner ℝ x v :=
  ⟨fun a b ↦ inner_add_left a b v, fun c a ↦ real_inner_smul_left a v c⟩
