-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.reciprocal_block_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:01:41.943239+00:00
-- url     : https://prove2.me/submissions/6358e64b-a777-4d7e-84ba-d5311b783f1d

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

namespace PaperR11
end PaperR11

/-!
# Exact weighted floor blocks for the actual thirteen intervals

Rewrites the weighted totient sum as thirteen reciprocal floor blocks.
The lower reciprocal endpoint is strict and the upper one weak. This file
constructs the literal finite weighted sums and identifies each block with
a difference of totient prefixes. It does not label this finite identity as
an asymptotic estimate or assume a summatory-totient error bound.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n l k u v : ℝ) (hl : 0 < l)
    (hk : 0 ≤ k) (hu : 0 < u) (huv : u < v) :
    k + u ≤ n / l ∧ n / l < k + v ↔
      n / (k + v) < l ∧ l ≤ n / (k + u) := by
  have hku : 0 < k + u := by linarith
  have hkv : 0 < k + v := by linarith
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hkv).2
      simpa only [mul_comm] using (div_lt_iff₀ hl).1 hhi
    · apply (le_div_iff₀ hku).2
      simpa only [mul_comm] using (le_div_iff₀ hl).1 hlo
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hl).2
      simpa only [mul_comm] using (le_div_iff₀ hku).1 hhi
    · apply (div_lt_iff₀ hl).2
      simpa only [mul_comm] using (div_lt_iff₀ hkv).1 hlo
