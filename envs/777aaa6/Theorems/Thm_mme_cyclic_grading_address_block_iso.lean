-- Prove2me | Theorems.Thm_mme_cyclic_grading_address_block_iso
-- name    : mme_cyclic_grading_address_block_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:46:45.05557+00:00
-- url     : https://prove2.me/theorems/01e01a47-8bf5-4718-b5a1-927fb5b1e30e
-- title:
--   A cyclic graded word block factors into three permuted word blocks
-- statement:
--   Let $G$ be a finite grading of a three-mode tensor and let $a,b,c$ be three length-$N$ words of grade triples. The block indexed by their coordinatewise cyclic product address is isomorphic to the Kronecker product of the three individual word blocks, with the second and third blocks cyclically permuted once and twice:
--
--   $$
--   B_{\mathrm{cyc}}(a,b,c) \cong
--   B_G(a)\otimes \pi B_G(b)\otimes \pi^2 B_G(c).
--   $$
--
--   This word-level factorization lifts the one-coordinate product-grading identity through an arbitrary tensor power. It is the algebraic bridge used to attach component-value extractions to retained cyclic laser-method edges.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic product and component extraction in Lemma 5.1, pp. 364--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The word-level identity is the multiplicative lift of the standard product-grading block factorization.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_cyclic_triple_grading
import Theorems.Thm_mme_cyclic_triple_grading_block_subtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators TensorObj.TypeGrading

universe u

set_option autoImplicit false

theorem mme_cyclic_grading_address_block_iso
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t)
    (a b c : Fin 3 → Fin N → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (gradedAddressBlock G a)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (gradedAddressBlock G b))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (gradedAddressBlock G c))))
      (gradedAddressBlock (mmeCyclicTripleGrading G)
        (fun i j ↦ mmeCyclicTripleGrade
          (fun s ↦ a s j) (fun s ↦ b s j) (fun s ↦ c s j) i)) := by
  sorry
