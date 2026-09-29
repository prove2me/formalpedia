-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_edge_cardinalities
-- name    : mme_stothers_phi233_cyclic_edge_cardinalities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:36:58.052264+00:00
-- url     : https://prove2.me/theorems/e58baa9b-5e20-4a4b-8259-18464fa33608
-- title:
--   Cubic cardinalities of exact and ambient phi_233 cyclic edges
-- statement:
--   For a fixed $\varphi_{233}$ profile, a cyclic exact edge is an ordered triple of exact-profile address words, and a cyclic ambient edge is an ordered triple of arbitrary supported words with the same three mode marginals. Consequently,
--
--   $$
--   |T_{\mathrm{cyc}}|=|S_0|^3,\qquad |A_{\mathrm{cyc}}|=|S|^3.
--   $$
--
--   This identifies the exact cubic cardinality ratio consumed by the cyclic type-2 hashing argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic symmetrization and Lemma 3.3 together with Lemma 5.1(v), pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_edge_cardinalities
    (N alpha beta gamma delta : ℕ) :
    Nat.card
        (MME.StothersFourth.Phi233.CyclicExactEdge
          N alpha beta gamma delta) =
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta)) ^ 3 ∧
      Nat.card
        (MME.StothersFourth.Phi233.CyclicAmbientEdge
          N alpha beta gamma delta) =
        (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta)) ^ 3 := by
  sorry
