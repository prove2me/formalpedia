-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
-- name    : mme_stothers_phi233_cyclic_finset_cardinalities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:42:04.353701+00:00
-- url     : https://prove2.me/theorems/1a710646-ced8-4526-a024-9bf9ce3a2429
-- title:
--   Exact inclusion and cardinalities of the phi_233 cyclic families
-- statement:
--   Let $T_{\mathrm{cyc}}$ be the concrete cyclic target finset of exact $\varphi_{233}$ profiles, and let $A_{\mathrm{cyc}}$ be the full cyclic finset of supported same-marginal completions. Then
--
--   $$
--   T_{\mathrm{cyc}}\subseteq A_{\mathrm{cyc}},\qquad |T_{\mathrm{cyc}}|=|S_0|^3,\qquad |A_{\mathrm{cyc}}|=|S|^3.
--   $$
--
--   This is the finite-cardinality interface used directly by the cyclic affine-hash incidence calculation.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic symmetrization and Lemma 3.3 together with Lemma 5.1(v), pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_finset_cardinalities
    (N alpha beta gamma delta : ℕ) :
    MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta ⊆
      MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta ∧
    (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card =
      (Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta)) ^ 3 ∧
    (MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta).card =
      (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta)) ^ 3 := by
  sorry
