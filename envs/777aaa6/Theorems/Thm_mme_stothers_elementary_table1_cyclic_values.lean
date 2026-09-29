-- Prove2me | Theorems.Thm_mme_stothers_elementary_table1_cyclic_values
-- name    : mme_stothers_elementary_table1_cyclic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:47:27.386624+00:00
-- url     : https://prove2.me/theorems/4039292c-862b-4e53-af48-1f2f5a0cdc56
-- title:
--   Elementary cyclic values for the first five Stothers classes
-- statement:
--   For $2\le 3\tau\le3$, each of the five elementary Table-1 classes $008,017,026,035,044$ has the cyclic tau-value stated by Davie and Stothers: its cyclic symmetrization attains every nonnegative strict lower value below the corresponding entry $v_0,\ldots,v_4$ of Table 1. These are the explicitly decomposable, nonrecursive constituents; the theorem deliberately excludes the five Lemma-5.1 recursive classes.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Table 1, first five rows, and the elementary constituent decompositions cited immediately before Lemma 5.1, printed p. 366; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis, 2010, Section 4.2; https://era.ed.ac.uk/handle/1842/4734.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_elementary_table1_cyclic_values
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ (i : Fin 5) (V : ℝ),
      0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau
        ⟨i.val, by omega⟩ →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 0)
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 1)
            (MME.StothersFourth.classRep ⟨i.val, by omega⟩ 2)))
        tau V := by
  sorry
