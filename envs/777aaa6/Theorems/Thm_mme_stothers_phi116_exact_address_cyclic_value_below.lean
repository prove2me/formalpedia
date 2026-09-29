-- Prove2me | Theorems.Thm_mme_stothers_phi116_exact_address_cyclic_value_below
-- name    : mme_stothers_phi116_exact_address_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:48:37.960317+00:00
-- url     : https://prove2.me/theorems/0f5f3b93-9afb-4bb5-ae9d-a5639539b495
-- title:
--   Cyclic tau-value of a factored phi_116 exact-address block
-- statement:
--   Let an exact supported $\varphi_{116}$ address of profile $(\alpha,\beta)$ be factored into its two recursive powers and two rectangular powers. Choose positive strict targets $W_0,W_1<L(6,\tau)$ and $W_2,W_3<E(6,\tau)^2$. Then the cyclic symmetrization of the literal address block has tau-value at least $$\prod_{r=0}^3\frac{W_r^{m_r}}2=\frac1{16}W_0^\alpha W_1^\alpha W_2^\beta W_3^\beta,$$ where $(m_0,m_1,m_2,m_3)=(\alpha,\alpha,\beta,\beta)$. The explicit constant loss is independent of address length and can be absorbed in the cofinal profile limit.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21; exact-address factorization and finite multiplicativity of cyclic tau-value.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_exact_address_cyclic_value_below
    {K : Type u} [Field K] (tau : ℝ)
    (htau : 2 ≤ 3 * tau)
    {N alpha beta : ℕ}
    (address : CWQ6ExactCoupledAddress N alpha beta)
    (hfactor :
      TensorObj.Restrict
        (TensorObj.kronFin 4 (fun r ↦
          (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
            (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
              alpha beta r)))
        (gradedAddressBlock
          (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K) address.1))
    (W : Fin 4 → ℝ)
    (hWpos : ∀ r, 0 < W r)
    (hWcoupled : W 0 < MME.StothersFourth.L 6 tau ∧
      W 1 < MME.StothersFourth.L 6 tau)
    (hWrect : W 2 < MME.StothersFourth.E 6 tau ^ (2 : ℕ) ∧
      W 3 < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (gradedAddressBlock
          (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K) address.1)) tau
      (∏ r : Fin 4,
        (W r ^
          MME.StothersFourth.Phi116.phi116ComponentMultiplicity alpha beta r) /
          2) := by
  sorry
