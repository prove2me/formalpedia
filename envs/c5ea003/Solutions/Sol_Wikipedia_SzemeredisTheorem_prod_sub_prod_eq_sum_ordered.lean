-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.prod_sub_prod_eq_sum_ordered
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:42.191961+00:00
-- url     : https://prove2.me/submissions/cc50b503-5c2a-4080-bf73-a97dcee3163c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Difference of two finite products, telescoped in the ambient linear
order.  Earlier factors use `f`, later factors use `g`. -/
theorem solution
    {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f g : ι → ℝ) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i =
      ∑ i ∈ s,
        (f i - g i) *
          (∏ j ∈ s with j < i, f j) *
          ∏ j ∈ s with i < j, g j := by
  have h :=
    Finset.prod_add_ordered s g (fun i => f i - g i)
  have hleft :
      (∏ i ∈ s, (g i + (f i - g i))) =
        ∏ i ∈ s, f i := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  have hlower (i : ι) :
      (∏ j ∈ s with j < i,
          (g j + (f j - g j))) =
        ∏ j ∈ s with j < i, f j := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hleft] at h
  simp_rw [hlower] at h
  linarith
