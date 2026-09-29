-- Prove2me | Theorems.Thm_mme_CWTensor_square_canonical_term_sum
-- name    : mme_CWTensor_square_canonical_term_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:09:36.112374+00:00
-- url     : https://prove2.me/theorems/41212ce6-a9a9-4521-a9c4-f26cd84f4362
-- title:
--   Canonical finite-term expansion of the square of the CW tensor
-- statement:
--   For every field $K$ and integer $q\ge 0$, the square of the basic Coppersmith--Winograd tensor expands as
--
--   $$
--   CW_q^{\otimes 2}=\sum_{t_2}\sum_{t_1}m_{t_1}\otimes m_{t_2}.
--   $$
--
--   This is the bilinear finite-sum expansion of the canonical term decomposition, and isolates one reusable level of the literal fourth-power calculation.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions (1990), definition of the basic tensor, journal p. 254, https://www.sciencedirect.com/science/article/pii/S0747717108800132; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Definitions.Def_mme_stothers_phi116_term_expansion
import Theorems.Thm_mme_CWTensor_canonical_term_sum

open MME TensorProduct BigOperators

universe u

set_option autoImplicit false

theorem mme_CWTensor_square_canonical_term_sum
    (K : Type u) [Field K] (q : ℕ) :
    interchange (CWTensor K q) (CWTensor K q) =
      ∑ t₂ : MME.StothersFourth.Phi116.CWTerm q,
      ∑ t₁ : MME.StothersFourth.Phi116.CWTerm q,
        interchange
          (MME.StothersFourth.Phi116.cwTermMonom K q t₁)
          (MME.StothersFourth.Phi116.cwTermMonom K q t₂) := by
  sorry
