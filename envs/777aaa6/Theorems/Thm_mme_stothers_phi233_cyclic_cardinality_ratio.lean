-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_cardinality_ratio
-- name    : mme_stothers_phi233_cyclic_cardinality_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:19:18.710629+00:00
-- url     : https://prove2.me/theorems/f2bc523a-5728-4285-abcc-89d20753be14
-- title:
--   Cubic lift of the phi_233 completion ratio
-- statement:
--   Fix an integral $\varphi_{233}$ profile. Let $S_0$ be its one-coordinate exact-profile address family and $S$ its same-marginal completion family. If $|S| \le R|S_0|$, then the threefold cyclic ambient and target families satisfy
--
--   $$
--   |A_{\mathrm{cyc}}| \le R^3 |T_{\mathrm{cyc}}|.
--   $$
--
--   The theorem is the exact finite cardinality bridge from a one-coordinate entropy estimate to the cyclic three-mode family used by affine hashing. It preserves the full explicit loss factor, cubed only because cyclic symmetrization takes three independent address coordinates.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, cyclic symmetrization in Section 3.2 and the exceptional phi_233 constituent in Lemma 5.1(v), pp. 359--360 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_cardinality_ratio
    (N alpha beta gamma delta : ℕ) (R : ℝ)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    ((MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta).card : ℝ) ≤
      R ^ 3 *
        ((MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta).card : ℝ) := by
  sorry
