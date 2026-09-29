-- Prove2me | solution 1 for mme_CW_2376_all_exact_target_edges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:55:45.359166+00:00
-- url     : https://prove2.me/submissions/6c757fcb-c561-464c-aa30-a2d864b3ec7b

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_exact_profile_address_supported
import Theorems.Thm_mme_CW_2376_exact_profile_address_marginals

open MME

set_option autoImplicit false

/-- The complete target subset of the full marginal hypergraph is in
bijection with the original exact-profile address type. -/
theorem solution
    (m : ℕ) :
    (cw2376AllExactTargetEdges m).card =
      Nat.card (CW2376ExactProfileAddress m) := by
  classical
  letI : Fintype (CW2376ProfileAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (cw2376ProfileLength m) → Fin 5))
  letI : Fintype (CW2376MarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        CW2376CoordinatewiseSupported a ∧ CW2376MarginallyRegular a})
  letI : Fintype (CW2376ExactProfileAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        ∀ sigma : Fin 3 → Fin 5,
          (Finset.univ.filter
            (fun j => cw2376AddressType a j = sigma)).card =
              cw2376ProfileMultiplicity m sigma})
  let e : CW2376ExactProfileAddress m ≃
      {a : CW2376MarginalSupportedAddress m //
        a ∈ cw2376AllExactTargetEdges m} := {
    toFun a := by
      have hmarginal : CW2376MarginallyRegular a.1 := by
        intro i r
        have h := mme_CW_2376_exact_profile_address_marginals m a i
        fin_cases r
        · simpa only [cw2376MarginalMultiplicity] using h.1
        · simpa only [cw2376MarginalMultiplicity] using h.2.1
        · simpa only [cw2376MarginalMultiplicity] using h.2.2.1
        · simpa only [cw2376MarginalMultiplicity] using h.2.2.2.1
        · simpa only [cw2376MarginalMultiplicity] using h.2.2.2.2
      let b : CW2376MarginalSupportedAddress m :=
        ⟨a.1, mme_CW_2376_exact_profile_address_supported m a,
          hmarginal⟩
      refine ⟨b, ?_⟩
      simp only [cw2376AllExactTargetEdges, cw2376ExactTargetEdges,
        Finset.mem_filter, cw2376MarginalSupportedUniverse,
        Finset.mem_univ, true_and, CW2376HasExactJointProfile]
      exact a.2
    invFun b := by
      refine ⟨b.1.1, ?_⟩
      have hb := b.2
      simp only [cw2376AllExactTargetEdges, cw2376ExactTargetEdges,
        Finset.mem_filter, CW2376HasExactJointProfile] at hb
      exact hb.2
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
  }
  calc
    (cw2376AllExactTargetEdges m).card =
        Fintype.card
          {a : CW2376MarginalSupportedAddress m //
            a ∈ cw2376AllExactTargetEdges m} := by simp
    _ = Fintype.card (CW2376ExactProfileAddress m) :=
      (Fintype.card_congr e).symm
    _ = Nat.card (CW2376ExactProfileAddress m) :=
      Nat.card_eq_fintype_card.symm
