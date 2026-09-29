-- Prove2me | solution 1 for CompressionLasVegas.lasVegas_bound_tight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:15:47.055225+00:00
-- url     : https://prove2.me/submissions/57735828-fb79-4337-a1ce-37d5fdc7f8f8

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open scoped Classical in
open CompressionOWF CompressionLasVegas in
theorem solution (i j s : ℕ) :
    (∀ y ∈ bitStrings (j + s), 2 ^ i ≤ (goodSeeds (prefixSeeded (j := j) (i := i)) s y).card) ∧
      Fintype.card ((Fin j → Bool) × (Fin i → Bool)) * (2 ^ (s + 1) - 1)
        < 2 * (2 ^ i * (bitStrings (j + s)).card) := by
  have hpre : ∀ {i j s : ℕ} (y : Str), y.length = j + s →
      2 ^ i ≤ (goodSeeds (prefixSeeded (j := j) (i := i)) s y).card := by
    intro i j s y hy
    let v : Fin j → Bool := fun t => y[(t : ℕ)]'(by omega)
    have hv : List.ofFn v = y.take j := by
      apply List.ext_getElem
      · simp
        omega
      · intro n h1 h2
        simp [v]
    have hsub : (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v))
        ⊆ goodSeeds (prefixSeeded (j := j) (i := i)) s y := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [goodSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
      have hD : prefixSeeded r (y.drop j) = y := by
        unfold prefixSeeded
        rw [hr, hv, List.take_append_drop]
      refine ⟨⟨_, hD⟩, ?_⟩
      have hK : K (prefixSeeded r) y ≤ (y.drop j).length := Nat.sInf_le ⟨_, rfl, hD⟩
      simp only [List.length_drop, hy] at hK
      omega
    have hcard : (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)).card = 2 ^ i := by
      have hset : Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)
          = ({v} : Finset (Fin j → Bool)) ×ˢ (Finset.univ : Finset (Fin i → Bool)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, and_true]
      rw [hset, Finset.card_product]
      simp
    calc 2 ^ i = (Finset.univ.filter (fun r : (Fin j → Bool) × (Fin i → Bool) => r.1 = v)).card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hbmem : ∀ {n : ℕ} (y : Str), y ∈ bitStrings n → y.length = n := by
    intro n y hy
    unfold bitStrings at hy
    rw [Finset.mem_image] at hy
    obtain ⟨v, _, rfl⟩ := hy
    simp
  have hbcard : ∀ n : ℕ, (bitStrings n).card = 2 ^ n := by
    intro n
    unfold bitStrings
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  refine ⟨fun y hy => hpre y (hbmem y hy), ?_⟩
  rw [hbcard]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hp : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  have h1 : 2 ^ j * 2 ^ i * (2 ^ (s + 1) - 1) < 2 ^ j * 2 ^ i * 2 ^ (s + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have h2 : 2 * (2 ^ i * 2 ^ (j + s)) = 2 ^ j * 2 ^ i * 2 ^ (s + 1) := by
    rw [pow_add, pow_succ]
    ring
  omega
