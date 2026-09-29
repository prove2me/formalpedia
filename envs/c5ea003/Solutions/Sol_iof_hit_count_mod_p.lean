-- Prove2me | solution 1 for iof_hit_count_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:37.058193+00:00
-- url     : https://prove2.me/submissions/2c0fa1d1-a94d-4cfa-b01c-35d79ae6d3f0

-- Sol generated from MachineLearning/Neural/NeuralFactorSearch.lean
import Mathlib

/-! # CatalogBuild.MachineLearning.Neural.NeuralFactorSearch

Auto-generated from theorem catalog database.
Domain: MachineLearning/Neural
Declarations: 8
-/































theorem solution(p : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    (Finset.univ.filter (fun k : ZMod p => (2 : ZMod p) * k = 1 ∨ (2 : ZMod p) * k = -1)).card = 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Let $r_1$ be the unique element in $\mathbb{Z}/p\mathbb{Z}$ such that $2r_1 = 1$, and let $r_2$ be the unique element in $\mathbb{Z}/p\mathbb{Z}$ such that $2r_2 = -1$.
  obtain ⟨r1, hr1⟩ : ∃ r1 : ZMod p, 2 * r1 = 1 := by
    exact ⟨ 2⁻¹, mul_inv_cancel₀ ( by erw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two ( lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ) ) ⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ZMod p, 2 * r2 = -1 := by
    exact ⟨ -r1, by linear_combination' -hr1 ⟩;
  have h_roots : ∀ k : ZMod p, 2 * k = 1 ∨ 2 * k = -1 ↔ k = r1 ∨ k = r2 := by
    grind +ring;
  rw [ Finset.card_eq_two ];
  refine' ⟨ r1, r2, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  grind
