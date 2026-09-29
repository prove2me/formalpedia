-- Prove2me | solution 1 for PosetFlow.ChainFrom.restrictLeft_concat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:51:23.898754+00:00
-- url     : https://prove2.me/submissions/09b21f91-744b-4edb-a70d-66e52f9e7876

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
-- NOTE: the target's statement passes the proof term `mem_concat_middle C D` to
-- `restrictLeft`. That lemma is available here only as an unproved stub mirror, so importing
-- it would contaminate this solution's axioms. Proofs are irrelevant, so the direct term
-- `Finset.mem_union_left _ C.mem_target` gives a definitionally equal statement instead.
open PosetFlow PosetFlow.ChainFrom in
theorem solution {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P] {x y z : P}
    (C : ChainFrom x y) (D : ChainFrom y z) :
    restrictLeft (concat C D) (Finset.mem_union_left _ C.mem_target) = C := by
  apply ChainFrom.ext
  show (C.carrier ∪ D.carrier).filter (· ≤ y) = C.carrier
  ext a
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨ha | ha, hay⟩
    · exact ha
    · -- an element of `D` lying below `y` must be `y` itself, which `C` contains
      have hya : y ≤ a := (D.bounded ha).1
      rw [le_antisymm hay hya]
      exact C.mem_target
  · intro ha
    exact ⟨Or.inl ha, (C.bounded ha).2⟩
