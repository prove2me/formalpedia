-- Prove2me | solution 1 for PosetFlow.alternatingSum_orderComplex_eq_zero_of_conePoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:47:51.669034+00:00
-- url     : https://prove2.me/submissions/d9655798-2698-4018-9bb7-4ee4180df5e2

-- Sol generated from Algebra/PosetFlow/OrderComplexEuler.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
import Theorems.Thm_PosetFlow_mem_orderComplex

/-!
# The order complex of a finite poset and cone points

This file develops the combinatorial (Euler-characteristic) shadow of the statement
"the simplicial nerve of a poset with a least element is contractible", which is the
homotopical engine behind the *chain replacement of a poset flow*: the poset of
strictly increasing chains from `x` to `y` ordered by refinement has a least element
(the chain `{x, y}`), hence its nerve is contractible, hence the chain replacement of
a poset flow has contractible spaces of execution paths.

Since simplicial contractibility is not available at this level of the library, we
prove the exact numerical consequence: the (unreduced) alternating face sum of the
order complex of a finite poset possessing a *cone point* vanishes, i.e. the reduced
Euler characteristic of the order complex is `0`.  The proof is a sign-reversing
involution: adding or deleting the cone point.

## Main definitions

* `PosetFlow.IsOrderChain` : a finset of a poset is totally ordered.
* `PosetFlow.orderComplex` : the finset of all totally ordered finsets (the faces of
  the order complex, including the empty face).

## Main results

* `PosetFlow.alternatingSum_orderComplex_eq_zero_of_conePoint` : if some element of a
  finite poset is comparable with every element, the alternating sum
  `∑ (-1) ^ |C|` over all faces `C` vanishes.
* `PosetFlow.reducedEuler_eq_zero_of_conePoint` : the reduced form, a sum over
  nonempty faces equal to `-1`.
* `PosetFlow.alternatingSum_orderComplex_eq_zero_of_orderBot` /
  `..._of_orderTop` : the special cases of a least / greatest element.
-/

open PosetFlow

open Finset

variable {R : Type*} [PartialOrder R] [Fintype R] [DecidableEq R] [DecidableLE R]




omit [Fintype R] [DecidableEq R] [DecidableLE R] in
lemma IsOrderChain.subset {C D : Finset R} (hD : IsOrderChain D) (h : C ⊆ D) :
    IsOrderChain C := fun _ ha _ hb => hD _ (h ha) _ (h hb)



omit [Fintype R] [DecidableLE R] in
/-- Inserting an element comparable with everything into a chain gives a chain. -/
lemma IsOrderChain.insert_conePoint {z : R} (hz : ∀ a, z ≤ a ∨ a ≤ z) {C : Finset R}
    (hC : IsOrderChain C) : IsOrderChain (insert z C) := by
  intro a ha b hb
  rcases Finset.mem_insert.1 ha with rfl | ha
  · exact hz b
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact (hz a).symm
  exact hC _ ha _ hb






open PosetFlow in
theorem solution(z : R) (hz : ∀ a, z ≤ a ∨ a ≤ z) :
    ∑ C ∈ orderComplex R, (-1 : ℤ) ^ C.card = 0 := by
  classical
  refine Finset.sum_involution (fun C _ => if z ∈ C then C.erase z else insert z C)
    ?_ ?_ ?_ ?_
  · -- the two faces have opposite signs
    intro C _
    by_cases h : z ∈ C
    · simp only [if_pos h]
      have hcard : C.card = (C.erase z).card + 1 := (Finset.card_erase_add_one h).symm
      rw [hcard, pow_succ]
      ring
    · simp only [if_neg h, Finset.card_insert_of_notMem h, pow_succ]
      ring
  · -- no fixed points
    intro C _ _
    by_cases h : z ∈ C
    · simp only [if_pos h]
      intro hC
      have hz' : z ∈ C.erase z := by rw [hC]; exact h
      exact Finset.notMem_erase z C hz'
    · simp only [if_neg h]
      intro hC
      exact h (by rw [← hC]; exact Finset.mem_insert_self z C)
  · -- the involution stays inside the order complex
    intro C hC
    rw [mem_orderComplex] at hC ⊢
    by_cases h : z ∈ C
    · simp only [if_pos h]; exact IsOrderChain.subset hC (Finset.erase_subset _ _)
    · simp only [if_neg h]; exact IsOrderChain.insert_conePoint hz hC
  · -- it is an involution
    intro C _
    by_cases h : z ∈ C
    · simp only [if_pos h, if_neg (Finset.notMem_erase z C)]
      exact Finset.insert_erase h
    · simp only [if_neg h, if_pos (Finset.mem_insert_self z C)]
      exact Finset.erase_insert h
