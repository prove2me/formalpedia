-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
-- name    : mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:46:29.552263+00:00
-- url     : https://prove2.me/theorems/1e93857a-de7c-4b4b-a8fb-99a6a55c4faf
-- title:
--   An exact phi_134 fine word restricts its literal outer address block
-- statement:
--   Fix an exact length-$2N$ profile address $x$ for $\Phi_{1,3,4}$, and let $r_j$ be its unique fine label at coordinate $j$. The coordinatewise product of the corresponding literal fine blocks restricts the block of the internal five-grading indexed by the full three-mode address $x$:
--
--   $$
--   \bigotimes_{j<2N}F_{r_j}\;\le\;B(x).
--   $$
--
--   This identifies the tensor obtained from the eight fine constituent atlas with the exact graded-address block that appears in the induced-matching and hashing theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii) and the type-2 hashing construction, printed pp. 366--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi134_exact_label
import Definitions.Def_mme_stothers_phi134_outer_grading

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi134.fineSourceObj K q
          (MME.StothersFourth.Phi134.exactLabelAt address j)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi134.outerGrading K q) address.1.1) := by
  sorry
