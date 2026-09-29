-- Prove2me | solution 1 for mme_modern_three_mode_common_shuffle_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:02:46.245487+00:00
-- url     : https://prove2.me/submissions/aa91bffb-4217-4cf3-bc4d-411e6118f61e

import Definitions.Def_mme_dwz_hole_cover_data
import Mathlib.Tactic

open BigOperators Finset MME.DWZSquare

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem uniform_preimage_subset_card
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block]
    [Fintype Shuffle] [DecidableEq Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (Q : Finset Block) (block : Block) :
    (univ.filter (fun g : Shuffle ↦
      (system.move g).symm block ∈ Q)).card * Fintype.card Block =
      Q.card * Fintype.card Shuffle := by
  classical
  let preimage : Shuffle → Block := fun g ↦ (system.move g).symm block
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset Shuffle) Q preimage
  calc
    (univ.filter (fun g : Shuffle ↦
        (system.move g).symm block ∈ Q)).card * Fintype.card Block =
        (∑ source ∈ Q,
          (univ.filter (fun g : Shuffle ↦ preimage g = source)).card) *
            Fintype.card Block := by rw [hpartition]
    _ = ∑ source ∈ Q,
        (univ.filter (fun g : Shuffle ↦ preimage g = source)).card *
          Fintype.card Block := by rw [Finset.sum_mul]
    _ = ∑ _source ∈ Q, Fintype.card Shuffle := by
      apply Finset.sum_congr rfl
      intro source _
      have heq :
          univ.filter (fun g : Shuffle ↦ preimage g = source) =
            univ.filter (fun g : Shuffle ↦ system.move g source = block) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, preimage,
          Equiv.symm_apply_eq]
        exact eq_comm
      rw [heq]
      exact system.uniform_fiber source block
    _ = Q.card * Fintype.card Shuffle := by simp

private theorem intersection_sum_uniform
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block]
    [Fintype Shuffle] [DecidableEq Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (P Q : Finset Block) :
    (∑ g : Shuffle,
      (P ∩ Q.image (system.move g)).card * Fintype.card Block) =
      Fintype.card Shuffle * (P.card * Q.card) := by
  classical
  have hinter : ∀ g : Shuffle,
      P ∩ Q.image (system.move g) =
        P.filter (fun block ↦ (system.move g).symm block ∈ Q) := by
    intro g
    ext block
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hp, x, hx, heq⟩
      exact ⟨hp, by simpa only [← heq, Equiv.symm_apply_apply] using hx⟩
    · rintro ⟨hp, hq⟩
      exact ⟨hp, (system.move g).symm block, hq, Equiv.apply_symm_apply _ _⟩
  have hswap :
      ∑ g : Shuffle, (P ∩ Q.image (system.move g)).card =
        ∑ block ∈ P,
          (univ.filter (fun g : Shuffle ↦
            (system.move g).symm block ∈ Q)).card := by
    simp_rw [hinter, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [← Finset.sum_mul, hswap, Finset.sum_mul]
  calc
    (∑ block ∈ P,
        (univ.filter (fun g : Shuffle ↦
          (system.move g).symm block ∈ Q)).card * Fintype.card Block) =
        ∑ _block ∈ P, Q.card * Fintype.card Shuffle := by
      apply Finset.sum_congr rfl
      intro block _
      exact uniform_preimage_subset_card system Q block
    _ = Fintype.card Shuffle * (P.card * Q.card) := by simp; ring

theorem solution
    {Block : Fin 3 → Type u} {Shuffle : Type v}
    [∀ i, Fintype (Block i)] [∀ i, DecidableEq (Block i)]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (system : (i : Fin 3) → AvailableBlockShuffle (Block i) Shuffle)
    (P Q : (i : Fin 3) → Finset (Block i)) :
    ∃ g : Shuffle, ∀ i : Fin 3,
      ((P i) ∩ (Q i).image ((system i).move g)).card * Fintype.card (Block i) ≤
        4 * ((P i).card * (Q i).card) := by
  classical
  let mass : Fin 3 → ℕ := fun i ↦ (P i).card * (Q i).card
  let cost : Fin 3 → Shuffle → ℕ := fun i g ↦
    ((P i) ∩ (Q i).image ((system i).move g)).card * Fintype.card (Block i)
  let normalized : Fin 3 → Shuffle → ℝ :=
    fun i g ↦ (cost i g : ℝ) / (mass i : ℝ)
  have hcostsum : ∀ i,
      ∑ g : Shuffle, cost i g = Fintype.card Shuffle * mass i := by
    intro i
    exact intersection_sum_uniform (system i) (P i) (Q i)
  have hnonneg : ∀ i g, 0 ≤ normalized i g := by
    intro i g
    dsimp [normalized]
    positivity
  have hsum : ∀ i, ∑ g : Shuffle, normalized i g ≤ (Fintype.card Shuffle : ℝ) := by
    intro i
    change (∑ g : Shuffle, (cost i g : ℝ) / (mass i : ℝ)) ≤ _
    rw [← Finset.sum_div]
    have hcast : (∑ g : Shuffle, (cost i g : ℝ)) =
        (Fintype.card Shuffle : ℝ) * (mass i : ℝ) := by
      exact_mod_cast hcostsum i
    rw [hcast]
    by_cases hm : mass i = 0
    · simp [hm]
    · have hm' : (mass i : ℝ) ≠ 0 := by exact_mod_cast hm
      rw [mul_div_cancel_right₀ _ hm']
  have htotal :
      (∑ g : Shuffle, ∑ i : Fin 3, normalized i g) ≤
        ∑ _g : Shuffle, (3 : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ i : Fin 3, ∑ g : Shuffle, normalized i g) ≤
          ∑ _i : Fin 3, (Fintype.card Shuffle : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ hsum i)
      _ = ∑ _g : Shuffle, (3 : ℝ) := by simp [mul_comm]
  obtain ⟨g, _, hg⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htotal
  refine ⟨g, ?_⟩
  intro i
  change cost i g ≤ 4 * mass i
  by_cases hm : mass i = 0
  · have hzero : cost i g = 0 := by
      change (P i).card * (Q i).card = 0 at hm
      rcases Nat.mul_eq_zero.mp hm with hp | hq
      · simp [cost, Finset.card_eq_zero.mp hp]
      · simp [cost, Finset.card_eq_zero.mp hq]
    rw [hzero]
    exact Nat.zero_le _
  · have hmpos : (0 : ℝ) < (mass i : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hsingle : normalized i g ≤ ∑ j : Fin 3, normalized j g :=
      Finset.single_le_sum (fun j _ ↦ hnonneg j g) (Finset.mem_univ i)
    have hfour : (cost i g : ℝ) / (mass i : ℝ) ≤ 4 := by
      exact le_trans (le_trans hsingle hg) (by norm_num)
    have hbound : (cost i g : ℝ) ≤ 4 * (mass i : ℝ) :=
      (div_le_iff₀ hmpos).mp hfour
    exact_mod_cast hbound
