-- Prove2me | Theorems.Thm_mme_stothers_cwFourth_cyclic_block_iso
-- name    : mme_stothers_cwFourth_cyclic_block_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:04:13.368959+00:00
-- url     : https://prove2.me/theorems/0408060f-6a9a-4052-9ce8-62096d04f2ef
-- title:
--   Canonical fourth CW blocks are equivariant under cyclic mode rotation
-- statement:
--   Let $T_q^{\otimes 4}$ carry its canonical grading by the nine total CW grades, and let $T_\rho$ denote the block selected by an ordered grade triple $\rho$.  If $c$ cyclically rotates the three tensor modes, then the block selected by $\rho\circ c^{-1}$ is tensor-isomorphic to the cyclic mode rotation of the original block:
--
--   $$T_{\rho\circ c^{-1}}\cong c\cdot T_\rho.$$
--
--   This q-parametric equivariance identifies the three literal blocks in every oriented cyclic orbit and is the tensor-level structural input to the Davie--Stothers Table 1 regrouping.
-- source:
--   The cyclic tensor-mode symmetry of the fourth Coppersmith--Winograd power used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_oriented_cyclic_classes

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_cwFourth_cyclic_block_iso
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        (MME.StothersFourth.fixedModeRelabel cyclicPerm ρ))
      (TensorObj.permObj cyclicPerm
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
          ρ)) := by
  sorry
