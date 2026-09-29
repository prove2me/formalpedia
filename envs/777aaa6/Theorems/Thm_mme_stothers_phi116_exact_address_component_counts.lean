-- Prove2me | Theorems.Thm_mme_stothers_phi116_exact_address_component_counts
-- name    : mme_stothers_phi116_exact_address_component_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:11:39.033187+00:00
-- url     : https://prove2.me/theorems/0dff94dc-5037-4f9d-a543-df9f87460aa2
-- title:
--   Exact four-component counts in a phi_116 outer address
-- statement:
--   Let an exact supported outer address have length $2N$ and profile parameters $\alpha+\beta=N$. Then the four supported outer types
--
--   $$000,\quad111,\quad012,\quad102$$
--
--   occur exactly $\alpha,\alpha,\beta,\beta$ times, respectively. The statement is uniform in $N,\alpha,$ and $\beta$ and supplies the exact fiber cardinalities for regrouping an address tensor into four component powers.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data

open MME

set_option autoImplicit false

theorem mme_stothers_phi116_exact_address_component_counts
    {N alpha beta : ℕ} (hsum : alpha + beta = N)
    (address : MME.CWQ6ExactCoupledAddress N alpha beta) :
    ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦
          MME.StothersFourth.Phi116.phi116OuterComponent address.1 j = u)).card =
        MME.StothersFourth.Phi116.phi116ComponentMultiplicity alpha beta u := by
  sorry
