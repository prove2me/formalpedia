-- Prove2me | Theorems.Thm_mme_stothers_phi116_fourth_tensor_term_expansion
-- name    : mme_stothers_phi116_fourth_tensor_term_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:21:53.571499+00:00
-- url     : https://prove2.me/theorems/40274f9f-61bd-4fa3-a0f4-da56b30840fd
-- title:
--   Canonical term expansion of the literal fourth CW power at q=6
-- statement:
--   The literal fourth power $CW_6^{\otimes4}$ is the fourfold finite sum of the ordered canonical CW monomials, with the parenthesization used by the Davie--Stothers source tensor. This specialization connects the public $\varphi_{116}$ term indexing to the already proved parameter-uniform literal fourth-power expansion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions (1990), definition of the basic tensor, journal p. 254, https://www.sciencedirect.com/science/article/pii/S0747717108800132; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Definitions.Def_mme_stothers_phi116_term_expansion

open MME TensorProduct Module BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_fourth_tensor_term_expansion
    (K : Type u) [Field K] :
    (MME.StothersFourth.cwFourthObj K 6).t =
      ∑ t₄ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₃ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₂ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₁ : MME.StothersFourth.Phi116.CWTerm 6,
        interchange
          (interchange
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₁)
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₂))
          (interchange
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₃)
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₄)) := by
  sorry
