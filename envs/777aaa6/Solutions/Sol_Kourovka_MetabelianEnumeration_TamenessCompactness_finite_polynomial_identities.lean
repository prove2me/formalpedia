-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.TamenessCompactness.finite_polynomial_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:56.231563+00:00
-- url     : https://prove2.me/submissions/52177943-89f6-41b7-af1a-ab2275b205aa

import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Theorems.Thm_Kourovka_MetabelianEnumeration_TamenessCompactness_finite_support_selection

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.TamenessCompactness
open ConeVerifier FiniteCover
namespace Kourovka.MetabelianEnumeration.TamenessCompactness
theorem _root_.solution {k a : ℕ} {G : Type*} [Group G]
    (t : Fin k → G) (A : Fin a → G)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 → ∃ p : Polynomial k,
      (∀ i, A i = polynomialWord t (A i) p) ∧
      ∀ u ∈ polynomialSupport p, 0 < dot u x) :
    ∃ polynomials : List (Polynomial k),
      (∀ p ∈ polynomials, ∀ i, A i = polynomialWord t (A i) p) ∧
        ConeCover (polynomials.map polynomialSupport) :=
  finite_support_selection polynomialSupport (fun p => ∀ i, A i = polynomialWord t (A i) p) h
end Kourovka.MetabelianEnumeration.TamenessCompactness
