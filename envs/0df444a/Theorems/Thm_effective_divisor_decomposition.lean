-- Prove2me | Theorems.Thm_effective_divisor_decomposition
-- name    : effective_divisor_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:35.43893+00:00
-- url     : https://prove2.me/theorems/a22a2d53-bb26-4b9a-9fef-a18b962782ce
-- title:
--   effective divisor decomposition: effective divisor decomposition
-- statement:
--   An effective divisor of degree $k_1+k_2$ can be decomposed into a sum of two effective
--   divisors of degrees $k_1$ and $k_2$, respectively.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L523-L626
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L523-L626

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty

theorem effective_divisor_decomposition (G : CFGraph) (E'' : CFDiv G) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv G),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by sorry
