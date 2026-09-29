-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_block_supports_mixed_addresses
-- name    : mme_stothers_phi233_cyclic_block_supports_mixed_addresses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:40:57.673776+00:00
-- url     : https://prove2.me/theorems/54e5ad27-27fb-436e-a726-0b9a458142d5
-- title:
--   Nonzero cyclic $\Phi_{233}$ blocks force all three mixed addresses to be supported
-- statement:
--   Consider three cyclic ambient edges selected modewise in the cyclic symmetrization of the coarse $\Phi_{233}$ constituent. Suppose that at every tensor-power coordinate, the block determined by those three selected mode vertices is nonzero. Then each of the three cyclically mixed three-mode addresses is coordinatewise one of the ten Davie--Stothers support types. Equivalently,
--
--   $$
--   \bigl(\forall j,\ B_{\mathrm{cyc}}(\sigma_j)\ne0\bigr)
--   \quad\Longrightarrow\quad
--   \operatorname{Supp}(x_0,y_1,z_2)\;\land\;
--   \operatorname{Supp}(y_0,z_1,x_2)\;\land\;
--   \operatorname{Supp}(z_0,x_1,y_2).
--   $$
--
--   This is the profile-specific compatibility condition needed to turn affine-hash vertex isolation into a direct-sum restriction of literal $\Phi_{233}$ tensor blocks.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic support pruning in Lemma 5.1(v), pp. 366--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_stothers_phi233_outer_grading
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_stothers_phi233_outer_grading_support

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_block_supports_mixed_addresses
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → MME.StothersFourth.Phi233.CyclicAmbientEdge
      N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading
        (MME.StothersFourth.Phi233.outerGrading K q)).blockTensor
        (fun i ↦
          MME.StothersFourth.Phi233.cyclicGradingAddress (es i) i j) ≠ 0) :
    MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
      (es 0) (es 1) (es 2) := by
  sorry
