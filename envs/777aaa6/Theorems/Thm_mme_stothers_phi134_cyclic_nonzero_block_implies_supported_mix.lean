-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_nonzero_block_implies_supported_mix
-- name    : mme_stothers_phi134_cyclic_nonzero_block_implies_supported_mix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-05T10:46:02.585791+00:00
-- url     : https://prove2.me/theorems/7d78adf9-0c1e-41ba-aa0c-e8094b1513c4
-- title:
--   A nonzero cyclic Phi_134 address block gives a supported modewise mixture
-- statement:
--   Take three cyclic exact-profile edges for $\Phi_{1,3,4}$ and mix their three address words in the cyclic mode order. If every coordinate block of the cyclic triple grading is nonzero, then all three resulting modewise mixtures lie in the eight fine support types of $\Phi_{1,3,4}$. In symbols, nonvanishing of every cyclic address coordinate implies the predicate
--
--   $$
--   \operatorname{CyclicCoordinatewiseSupported}(x,y,z).
--   $$
--
--   This is the support-detection bridge used to turn combinatorial inducedness into the nonvanishing hypothesis required by the generic induced-block restriction theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(iii), pp. 359--365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_cyclic_triple_grading
import Definitions.Def_mme_stothers_phi134_cyclic_grading_address
import Definitions.Def_mme_stothers_phi134_outer_grading

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_nonzero_block_implies_supported_mix
    {K : Type u} [Field K] {N alpha beta gamma delta : ℕ}
    (x y z : MME.StothersFourth.Phi134.CyclicExactEdge
      N alpha beta gamma delta)
    (hnz : ∀ j,
      (mmeCyclicTripleGrading
        (MME.StothersFourth.Phi134.outerGrading K 6)).blockTensor
        (fun i ↦ MME.StothersFourth.Phi134.cyclicGradingAddress
          (![x, y, z] i) i j) ≠ 0) :
    MME.StothersFourth.Phi134.CyclicCoordinatewiseSupported x y z := by
  sorry
