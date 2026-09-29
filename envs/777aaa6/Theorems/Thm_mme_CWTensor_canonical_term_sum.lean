-- Prove2me | Theorems.Thm_mme_CWTensor_canonical_term_sum
-- name    : mme_CWTensor_canonical_term_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:02:35.869674+00:00
-- url     : https://prove2.me/theorems/67055ba7-5fef-4cd3-9839-cb61678c39c2
-- title:
--   Canonical finite-term expansion of the Coppersmith--Winograd tensor
-- statement:
--   For every field $K$ and integer $q\ge 0$, the basic Coppersmith--Winograd tensor is the sum of its $3q+3$ canonical rank-one terms:
--
--   $$
--   CW_q=\sum_{t\in \mathrm{CWTerm}(q)}m_t.
--   $$
--
--   The index type separates the three cyclic families, each indexed by $i\in\{0,\ldots,q-1\}$, from the three exceptional terms. This identity is the algebraic input for distributing a fourth tensor power into a finite sum of ordered four-term products.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions (1990), definition of the basic tensor, journal p. 254, https://www.sciencedirect.com/science/article/pii/S0747717108800132; A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Definitions.Def_mme_stothers_phi116_term_expansion

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CWTensor_canonical_term_sum
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q =
      ∑ t : MME.StothersFourth.Phi116.CWTerm q,
        MME.StothersFourth.Phi116.cwTermMonom K q t := by
  sorry
