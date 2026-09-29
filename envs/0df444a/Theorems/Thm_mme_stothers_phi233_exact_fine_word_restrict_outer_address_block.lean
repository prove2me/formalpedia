-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_fine_word_restrict_outer_address_block
-- name    : mme_stothers_phi233_exact_fine_word_restrict_outer_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:21:30.687879+00:00
-- url     : https://prove2.me/theorems/e9993f57-80f4-4345-8aa4-a388765676dc
-- title:
--   An exact phi_233 fine word restricts its literal outer address block
-- statement:
--   Fix an exact length-$2N$ profile address $x$ for $\varphi_{233}$, and let $r_j$ be its unique fine label at coordinate $j$. The coordinatewise product of the corresponding literal fine blocks restricts the block of the internal five-grading indexed by the full three-mode address $x$:
--
--   $$
--   \bigotimes_{j<2N}F_{r_j}\;\le\;B(x).
--   $$
--
--   This identifies the tensor obtained from the ten fine constituent atlas with the exact graded-address block that appears in the induced-matching and hashing theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v) and the type-2 hashing construction, printed pp. 366--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi233_exact_label
import Theorems.Thm_mme_stothers_phi233_fine_source_restrict_outer_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_fine_word_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi233.outerGrading K q) address.1.1) := by
  sorry
