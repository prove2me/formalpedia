-- Prove2me | Theorems.Thm_mme_stothers_phi233_selected_entropy_minimizer_exists
-- name    : mme_stothers_phi233_selected_entropy_minimizer_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:15:12.084498+00:00
-- url     : https://prove2.me/theorems/cce70ecc-94f8-420c-84ff-1f486e234b4c
-- title:
--   Existence of the entropy-minimizing phi_233 profile
-- statement:
--   Let E,H,L be positive with E<L and H<L, and choose the phi_233 optimizer statistics sigma=2H/(2H+L) and mu=E/(E+L). Then the nonempty same-marginal profile fiber contains a profile minimizing the logarithm of a^(2a)b^b c^c d^d, where b=sigma-2a, c=mu-a, and d=1-sigma-mu+a. This supplies the minimizer invoked in Davie--Stothers Lemma 5.1(v) to make the same-marginal completion penalty equal to one.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), pp. 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

theorem mme_stothers_phi233_selected_entropy_minimizer_exists
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
      ∀ x ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
        (-2 * Real.negMulLog a -
            Real.negMulLog (sigma - 2 * a) -
            Real.negMulLog (mu - a) -
            Real.negMulLog (1 - sigma - mu + a)) ≤
          (-2 * Real.negMulLog x -
            Real.negMulLog (sigma - 2 * x) -
            Real.negMulLog (mu - x) -
            Real.negMulLog (1 - sigma - mu + x)) := by
  sorry
