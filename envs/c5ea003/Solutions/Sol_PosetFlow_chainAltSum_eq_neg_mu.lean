-- Prove2me | solution 1 for PosetFlow.chainAltSum_eq_neg_mu
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:54:39.984167+00:00
-- url     : https://prove2.me/submissions/1244785d-616b-482b-9bd8-cfc6a260aaa7

-- Sol generated from Algebra/PosetFlow/HallMobius.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
import Theorems.Thm_PosetFlow_chainAltSum_recursion
import Theorems.Thm_PosetFlow_chainFinsets_self
import Theorems.Thm_PosetFlow_mem_chainFinsets

/-!
# Philip Hall's theorem: chains of a poset compute its Möbius function

The chain replacement of a poset flow replaces the (one point) spaces of execution
paths of a poset flow by the nerves of the refinement posets of chains.  The Euler
characteristics of those nerves are governed by the classical theorem of Philip
Hall, which identifies the alternating sum over chains from `x` to `y` with the
Möbius function of the incidence algebra.

This file proves Hall's theorem in the form

`∑ C ∈ chainFinsets x y, (-1) ^ |C| = - μ x y`,

where `chainFinsets x y` is the finite set of carriers of chains from `x` to `y`
(the objects of the refinement poset `PosetFlow.ChainFrom x y` of
`Algebra.PosetFlow.ChainPoset`), and `μ` is `IncidenceAlgebra.mu`.

## Main results

* `PosetFlow.chainAltSum_recursion` : deleting the top element `y` of a chain
  identifies chains from `x` to `y` with pairs `(z, C)` where `z ∈ Ico x y` and `C`
  is a chain from `x` to `z`.  This is the combinatorial induction step.
* `PosetFlow.chainAltSum_eq_neg_mu` : **Philip Hall's theorem**.
* `PosetFlow.mu_eq_zero_of_not_le` : the Möbius function vanishes off the order,
  a corollary of the chain description.
-/

open PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]






@[simp] theorem chainAltSum_self (x : P) : chainAltSum x x = -1 := by
  rw [chainAltSum, chainFinsets_self]
  simp

theorem chainFinsets_eq_empty_of_not_le {x y : P} (h : ¬ x ≤ y) : chainFinsets x y = ∅ := by
  ext C
  simp only [mem_chainFinsets, Finset.notMem_empty, iff_false, not_and]
  intro _ hy hb
  exact absurd (hb y hy).1 h

theorem chainAltSum_of_not_le {x y : P} (h : ¬ x ≤ y) : chainAltSum x y = 0 := by
  rw [chainAltSum, chainFinsets_eq_empty_of_not_le h, Finset.sum_empty]



variable [LocallyFiniteOrder P]






open PosetFlow in
theorem solution(x y : P) : chainAltSum x y = -mu ℤ x y := by
  induction y using WellFoundedLT.induction with
  | _ y ih =>
    by_cases hxy : x = y
    · subst hxy
      simp
    · by_cases hle : x ≤ y
      · have hlt : x < y := lt_of_le_of_ne hle hxy
        rw [chainAltSum_recursion hlt, mu_apply, if_neg hxy, neg_neg,
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [Finset.mem_Ico] at hz
        rw [ih z hz.2, neg_neg]
      · rw [chainAltSum_of_not_le hle, mu_apply, if_neg hxy,
          Finset.Ico_eq_empty (fun h => hle (le_of_lt h))]
        simp
