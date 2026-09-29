-- Prove2me | solution 1 for mme_stothers_general_outer_hash_budget_of_bounded_degree_data
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T17:29:00.395594+00:00
-- url     : https://prove2.me/submissions/d780f4a8-3c20-4843-8352-1205b237c140

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_general_affine_hash
import Theorems.Thm_mme_stothers_general_hash_budget_of_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_behrend_margin_parameters

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem genFreeHashAllTargetEdges_card_eq_natCard
    (base : Fin 10 → ℕ) (m : ℕ) :
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

private theorem genFreeHashStar_card_eq_natCard
    (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3)
    (a : GenMarginalSupportedAddress base m) :
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
    (Dsmall Dbig : ℕ → ℕ)
    (hdata : ∀ᶠ m : ℕ in atTop,
      let N := genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
      (Nat.card
          {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a} : ℝ) = V * (Dsmall m : ℝ) ∧
        1 ≤ Dsmall m ∧ Dsmall m ≤ Dbig m ∧
        (∀ i : Fin 3,
          ∀ a : {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a},
          Nat.card
            {b : GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤ (6 * (N + 1)) ^ 100 * Dbig m) ∧
        (6 * (N + 1)) ^ 100 * Dbig m ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in atTop,
      let N := genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (GenMarginalSupportedAddress base m),
        GenMarginalVertexClosed E ∧
        ((genTargetAmbientCollisions E).card : ℝ) +
            V * ((Dsmall m : ℝ) / (Dbig m : ℝ)) *
              Real.exp
                (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((genExactTargetEdges E).card : ℝ) := by
  filter_upwards [hdata, eventually_gt_atTop 0] with m hmdata hm
  dsimp only at hmdata ⊢
  set N : ℕ := genOuterLength base m with hN
  set V : ℝ :=
    (N.factorial : ℝ) /
      ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ) with hVdef
  set D : ℕ := (6 * (N + 1)) ^ 100 * Dbig m with hD
  obtain ⟨hTcard, hDsmall, hDle, hdegreeCard, hD5⟩ := hmdata
  have hDbigPos : 1 ≤ Dbig m := le_trans hDsmall hDle
  have hT : ((genHashAllTargetEdges base m).card : ℝ) =
      V * (Dsmall m : ℝ) := by
    rw [genFreeHashAllTargetEdges_card_eq_natCard base]
    exact hTcard
  have hdeg : ∀ i : Fin 3, ∀ a ∈ genHashAllTargetEdges base m,
      ((genHashMarginalUniverse base m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D := by
    intro i a ha
    rw [genFreeHashStar_card_eq_natCard]
    apply hdegreeCard i
      (⟨a, ?_⟩ : {a : GenMarginalSupportedAddress base m //
        GenHasExactJointProfile a})
    simpa only [genHashAllTargetEdges, genHashMarginalUniverse,
      genExactTargetEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using ha
  obtain ⟨p, hpPrime, hp9, hpOdd, S, hSrange, hSfree, hmargin⟩ :=
    mme_stothers_fixed_behrend_margin_parameters N (Dbig m) hDbigPos hD5
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hV : 0 ≤ V := by
    rw [hVdef]; positivity
  set loss : ℝ :=
    Real.exp (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) with hloss
  have hbigReal : (0 : ℝ) < (Dbig m : ℝ) := by
    exact_mod_cast hDbigPos
  have hratio : (0 : ℝ) ≤ (Dsmall m : ℝ) / (Dbig m : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hbigReal.le
  have hmargin' :
      (p : ℝ) ^ 2 * (((Dsmall m : ℝ) / (Dbig m : ℝ)) * loss) +
          3 * (Dsmall m : ℝ) * (D : ℝ) ≤
        (Dsmall m : ℝ) * (S.card : ℝ) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hmargin hratio
    have hcancel : ((Dsmall m : ℝ) / (Dbig m : ℝ)) * (Dbig m : ℝ) =
        (Dsmall m : ℝ) := div_mul_cancel₀ _ hbigReal.ne'
    have hD' : (D : ℝ) = ((6 * (N + 1)) ^ 100 : ℕ) * (Dbig m : ℝ) := by
      rw [hD]; push_cast; ring
    nlinarith [hscaled, hcancel, hbigReal, hratio]
  have hfinal :=
    mme_stothers_general_hash_budget_of_degree base hbase m p D (Dsmall m)
      hm hp9 hpOdd S hSrange hSfree V
      (((Dsmall m : ℝ) / (Dbig m : ℝ)) * loss) hV hT hdeg hmargin'
  obtain ⟨E, hEclosed, hE⟩ := hfinal
  refine ⟨E, hEclosed, ?_⟩
  calc
    ((genTargetAmbientCollisions E).card : ℝ) +
        V * ((Dsmall m : ℝ) / (Dbig m : ℝ)) * loss =
        ((genTargetAmbientCollisions E).card : ℝ) +
          V * (((Dsmall m : ℝ) / (Dbig m : ℝ)) * loss) := by ring
    _ ≤ ((genExactTargetEdges E).card : ℝ) := hE
