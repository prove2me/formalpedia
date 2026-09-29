-- Prove2me | Theorems.Thm_mme_stothers_fixed_address_group_by_ordered_grade_types
-- name    : mme_stothers_fixed_address_group_by_ordered_grade_types
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:07:00.153425+00:00
-- url     : https://prove2.me/theorems/9d8a66d7-0445-49e4-8c69-c46cb4688c67
-- title:
--   Regroup an exact Stothers address by its 729 ordered grade types
-- statement:
--   Let $a$ be an exact fixed-profile Stothers address of length $N_m$. For each ordered grade triple $\sigma\in\{0,\ldots,8\}^3$, let $T_\sigma$ be the corresponding canonical fourth-power block and let $c_\sigma(m)$ be its prescribed joint multiplicity. Then the literal ordered address block is tensor-isomorphic to $$\bigboxtimes_{\sigma\in\{0,\ldots,8\}^3}T_\sigma^{\boxtimes c_\sigma(m)}.$$ The formal statement uses a canonical finite enumeration of the 729 ordered triples. Unsupported triples are included with multiplicity zero. This is an exact finite regrouping, with no asymptotic or numerical estimate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and the exact type decomposition used in Theorem 5.3, printed pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_address_group_by_ordered_grade_types
    {K : Type u} [Field K]
    (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m) :
    let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
      classical
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
        (Fintype.equivFin (Fin 3 → Fin 9))
    TensorObj.Isomorphic
      (gradedAddressBlock
        (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
      (TensorObj.kronFin 729 (fun s ↦
        ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
          (e.symm s)).kronPow
            (MME.StothersFourth.fixedJointMultiplicity m (e.symm s)))) := by
  sorry
