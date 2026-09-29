-- Prove2me | solution 1 for mme_stothers_phi116_exact_address_factor_exponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:13:44.862217+00:00
-- url     : https://prove2.me/submissions/60ca6d2a-fd59-44c6-9271-a86af621f92a

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Theorems.Thm_mme_stothers_phi116_exact_address_component_counts

open MME
open MME.StothersFourth.Phi116

set_option autoImplicit false
set_option warningAsError true

private theorem card_filter_two_values
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (t : A → B) (r s : B) (hrs : r ≠ s) :
    ((Finset.univ : Finset A).filter (fun j ↦ t j = r ∨ t j = s)).card =
      ((Finset.univ : Finset A).filter (fun j ↦ t j = r)).card +
        ((Finset.univ : Finset A).filter (fun j ↦ t j = s)).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro j hjr hjs
  have hr := (Finset.mem_filter.mp hjr).2
  have hs := (Finset.mem_filter.mp hjs).2
  exact hrs (hr.symm.trans hs)

theorem solution
    {N alpha beta : ℕ} (hsum : alpha + beta = N)
    (address : CWQ6ExactCoupledAddress N alpha beta) :
    let recursiveCount :=
      ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦
        phi116OuterComponent address.1 j = 0 ∨
          phi116OuterComponent address.1 j = 1)).card
    let rectangularCount :=
      ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦
        phi116OuterComponent address.1 j = 2 ∨
          phi116OuterComponent address.1 j = 3)).card
    recursiveCount = 2 * alpha ∧
      rectangularCount = 2 * beta ∧
      2 * rectangularCount = 4 * beta := by
  dsimp only
  have hcounts :=
    mme_stothers_phi116_exact_address_component_counts hsum address
  rw [card_filter_two_values
      (fun j ↦ phi116OuterComponent address.1 j) 0 1 (by decide),
    card_filter_two_values
      (fun j ↦ phi116OuterComponent address.1 j) 2 3 (by decide),
    hcounts 0, hcounts 1, hcounts 2, hcounts 3]
  simp [phi116ComponentMultiplicity]
  omega
