-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_profile_exact_counts
-- name    : mme_CW_q6_type2_cyclic_profile_exact_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:28:41.760451+00:00
-- url     : https://prove2.me/theorems/05f693b0-8492-476e-b7f8-6feb19471b84
-- title:
--   Exact cyclic mode count and degree for the four-edge type-2 profile
-- statement:
--   For the exact four-edge profile with multiplicities $(L,L,G,G)$ and $L+G=N$, the product of the three mode-word counts is $$ {2N\choose N}^{2}{2N\choose L}{2N-L\choose L}, $$ and the product of the three fixed-word degrees is uniformly $$ {N\choose G}^{4}{2G\choose G}. $$ These are the common mode size and common fiber degree after the three cyclic orientations in the type-2 Salem--Spencer extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3.2, equation (3.6), and Lemma 5.1(i), pp. 359-364.

import Definitions.Def_mme_CW_q6_exact_address_incidence

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_profile_exact_counts
    (N L G : ℕ) (hLG : L + G = N) :
    (cwQ6ExactXWords N L G).card * (cwQ6ExactYWords N L G).card * (cwQ6ExactZWords N L G).card = Nat.choose (2 * N) N ^ (2 : ℕ) * (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) ∧
      ∀ x ∈ cwQ6ExactXWords N L G, ∀ y ∈ cwQ6ExactYWords N L G, ∀ z ∈ cwQ6ExactZWords N L G,
        ((cwQ6ExactAddresses N L G).filter (fun e ↦ e 0 = x)).card * ((cwQ6ExactAddresses N L G).filter (fun e ↦ e 1 = y)).card * ((cwQ6ExactAddresses N L G).filter (fun e ↦ e 2 = z)).card = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  sorry
