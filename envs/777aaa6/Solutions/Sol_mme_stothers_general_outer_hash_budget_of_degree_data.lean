-- Prove2me | solution 1 for mme_stothers_general_outer_hash_budget_of_degree_data
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T17:23:11.442976+00:00
-- url     : https://prove2.me/submissions/97827f45-0213-4598-ae33-b9bac8f6d8f5

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_stothers_general_affine_hash
import Theorems.Thm_mme_stothers_general_hash_budget_of_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_behrend_margin_parameters

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem genHashAllTargetEdges_card_eq_natCard (base : Fin 10 → ℕ) (m : ℕ) :
    (genHashAllTargetEdges base m).card =
      Nat.card
        {a : GenMarginalSupportedAddress base m //
          GenHasExactJointProfile a} := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {a : GenOuterAddress base m //
        GenCoordinatewiseSupported a ∧ GenMarginallyRegular a})
  letI : Fintype
      {a : GenMarginalSupportedAddress base m //
        GenHasExactJointProfile a} := by
    infer_instance
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem genHashStar_card_eq_natCard
    (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3) (a : GenMarginalSupportedAddress base m) :
    ((genHashMarginalUniverse base m).filter
        (fun b ↦ b.1 i = a.1 i)).card =
      Nat.card
        {b : GenMarginalSupportedAddress base m // b.1 i = a.1 i} := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {b : GenOuterAddress base m //
        GenCoordinatewiseSupported b ∧ GenMarginallyRegular b})
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (hdata : ∀ᶠ m : ℕ in atTop,
      let N := genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
      let Dstar : ℕ :=
        (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
          ∏ sigma : {sigma : Fin 3 → Fin 9 //
              (∑ s, (sigma s).val) = 8},
            (genJointMultiplicity base m sigma.1).factorial
      let P := (6 * (N + 1)) ^ 100
      let D := P * Dstar
      (Nat.card
          {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a} : ℝ) = V * (Dstar : ℝ) ∧
        1 ≤ Dstar ∧
        (∀ i : Fin 3,
          ∀ a : {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a},
          Nat.card
            {b : GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤ D) ∧
        D ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in atTop,
      let N := genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (GenMarginalSupportedAddress base m),
        GenMarginalVertexClosed E ∧
        ((genTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((genExactTargetEdges E).card : ℝ) := by
  filter_upwards [hdata, eventually_gt_atTop 0] with m hmdata hm
  dsimp only at hmdata
  let N : ℕ := genOuterLength base m
  let V : ℝ :=
    (N.factorial : ℝ) /
      ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
  let Dstar : ℕ := genHashTargetStarDegree base m
  let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
  rcases hmdata with ⟨hTcard, hDstar, hdegreeCard, hD5⟩
  have hT : ((genHashAllTargetEdges base m).card : ℝ) =
      V * (Dstar : ℝ) := by
    rw [genHashAllTargetEdges_card_eq_natCard base]
    simpa only [V, Dstar, genHashTargetStarDegree,
      genHashTargetJointTable] using hTcard
  have hdeg : ∀ i : Fin 3, ∀ a ∈ genHashAllTargetEdges base m,
      ((genHashMarginalUniverse base m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D := by
    intro i a ha
    rw [genHashStar_card_eq_natCard]
    apply hdegreeCard i
      (⟨a, ?_⟩ : {a : GenMarginalSupportedAddress base m //
        GenHasExactJointProfile a})
    simpa only [genHashAllTargetEdges, genHashMarginalUniverse,
      genExactTargetEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using ha
  obtain ⟨p, hpPrime, hp9, hpOdd, S, hSrange, hSfree, hmargin⟩ :=
    mme_stothers_fixed_behrend_margin_parameters N Dstar hDstar
      (by simpa only [N, Dstar, D, genHashTargetStarDegree,
          genHashTargetJointTable] using hD5)
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hV : 0 ≤ V := by
    dsimp only [V]
    positivity
  simpa only [N, V] using
    mme_stothers_general_hash_budget_of_degree base hbase m p D Dstar hm hp9 hpOdd S hSrange hSfree
      V
      (Real.exp
        (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))))
      hV hT hdeg
      (by simpa only [D] using hmargin)

