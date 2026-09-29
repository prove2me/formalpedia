-- Prove2me | solution 2 for AlmostLossless.avg_decodeCost_bucketed_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:25:18.135839+00:00
-- url     : https://prove2.me/submissions/529eb41e-d4af-4148-9c47-645990d2ff17

import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
open AlmostLossless in
theorem solution {S : Type*} [DecidableEq S] {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [Fintype A₁]
    [DecidableEq A₁] [Nonempty A₁] [Fintype M₁] [Nonempty M₁]
    (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
    (hpi : PairwiseIndependent h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
    (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
        ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
      = 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by
  have hsumN : ∀ (x : S), (∑ a₁ : A₁, ((T.erase x).filter (fun y => h₁ a₁ y = h₁ a₁ x)).card)
      * Fintype.card M₁ = (T.erase x).card * Fintype.card A₁ := by
    intro x
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset A₁)) (t := T.erase x) (r := fun a₁ y => h₁ a₁ y = h₁ a₁ x)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
    rw [hdc, Finset.sum_mul]
    calc ∑ y ∈ T.erase x, (Finset.univ.filter (fun a₁ => h₁ a₁ y = h₁ a₁ x)).card * Fintype.card M₁
        = ∑ _y ∈ T.erase x, Fintype.card A₁ := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          exact hpi y x (Finset.ne_of_mem_erase hy)
      _ = (T.erase x).card * Fintype.card A₁ := by simp
  have hcost : ∀ a₁ : A₁, (bucketed T h₁ h₂).decodeCost (a₁, a₂) ((bucketed T h₁ h₂).hash (a₁, a₂) x)
      = 1 + ((T.erase x).filter (fun y => h₁ a₁ y = h₁ a₁ x)).card := by
    intro a₁
    show (T.filter (fun t => h₁ a₁ t = h₁ a₁ x)).card = _
    have hmem : x ∈ T.filter (fun t => h₁ a₁ t = h₁ a₁ x) := Finset.mem_filter.mpr ⟨hx, rfl⟩
    rw [Finset.filter_erase, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.mpr ⟨x, hmem⟩
    omega
  have hA : (0 : ℚ) < Fintype.card A₁ := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℚ) < Fintype.card M₁ := by exact_mod_cast Fintype.card_pos
  have hsumQ : (∑ a₁ : A₁, (((T.erase x).filter (fun y => h₁ a₁ y = h₁ a₁ x)).card : ℚ))
      * Fintype.card M₁ = ((T.erase x).card : ℚ) * Fintype.card A₁ := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsumN x
  simp_rw [hcost]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsum' : (∑ a₁ : A₁, (((T.erase x).filter (fun y => h₁ a₁ y = h₁ a₁ x)).card : ℚ))
      = ((T.erase x).card : ℚ) * Fintype.card A₁ / Fintype.card M₁ := by
    rw [eq_div_iff hM.ne']
    exact hsumQ
  rw [hsum']
  field_simp
