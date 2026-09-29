-- Prove2me | Theorems.Thm_mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
-- name    : mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:47:30.416963+00:00
-- url     : https://prove2.me/theorems/6ecadf31-86f9-4be7-8c90-d083be12e86a
-- title:
--   Assemble an exact Stothers address block from its ten cyclic class values
-- statement:
--   For a fixed value of $\tau$, suppose the cyclic symmetrization of the representative of each of the ten Davie--Stothers Table-1 classes attains every nonnegative strict lower bound below its advertised class value $v_r(\tau)$. Then every literal exact-profile address block at integral scale $m$ attains every nonnegative value strictly below $\prod_r v_r(\tau)^{n_r c_r(m)}$. The proof is the finite tensor-bookkeeping step: group address coordinates by their exact ordered grade triple, partition each Table-1 orbit into cyclic triples, transport the second cyclic orbit through a mode permutation when $n_r=2$, synchronize strict local witnesses, and reassemble the ordered Kronecker product. No entropy, hashing, or numerical inequality is part of this theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and the tensor-value substitution in the proof of Theorem 5.3, printed pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
    {K : Type u} [Field K]
    (tau : ℝ)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  sorry
