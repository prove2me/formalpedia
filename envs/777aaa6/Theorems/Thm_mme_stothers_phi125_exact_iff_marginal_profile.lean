-- Prove2me | Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile
-- name    : mme_stothers_phi125_exact_iff_marginal_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:51:23.432528+00:00
-- url     : https://prove2.me/theorems/e97fb135-a294-48a1-8a57-c5017e57c3f5
-- title:
--   The phi_125 symmetric profile is determined by its three marginals
-- statement:
--   Let α, β, γ be nonnegative integers with α+β+γ=N. Label the six summands of φ₁₂₅ by the square grades (004), (013), (022), (103), (112), and (121), and assign them target multiplicities (α,β,γ,γ,β,α). Then the six grade patterns are pairwise distinct, and a length-2N label word has those exact six multiplicities if and only if its three projected grade words have histograms $$ (N,N,0,0,0),\qquad (\alpha+\gamma,2\beta,\alpha+\gamma,0,0),\qquad (0,\alpha,\beta+\gamma,\beta+\gamma,\alpha). $$ Thus the same-marginal ambient profile equals the exact symmetric profile. This is the source-specific closure fact that removes the completion-ratio loss from the type-2 extraction for φ₁₂₅.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 5.1(ii), especially the displayed Q₁Γ, Q₂Γ, Q₃Γ marginals and the statement that they determine α, β, γ, printed pp. 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi125_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi125_exact_iff_marginal_profile
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Function.Injective MME.StothersFourth.Phi125.pattern ∧
    ∀ w : MME.StothersFourth.Phi125.ProfileWord N,
      ((∀ r : Fin 6,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => w j = r)).card =
            MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r) ↔
       (∀ i : Fin 3, ∀ s : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j =>
            MME.StothersFourth.Phi125.modeWord w i j = s)).card =
            MME.StothersFourth.Phi125.marginalMultiplicity
              N alpha beta gamma i s)) := by
  sorry
