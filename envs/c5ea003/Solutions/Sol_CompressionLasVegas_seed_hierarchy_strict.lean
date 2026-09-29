-- Prove2me | solution 1 for CompressionLasVegas.seed_hierarchy_strict
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:20:59.374033+00:00
-- url     : https://prove2.me/submissions/849ddf93-4a84-4456-923c-6979f2152ce2

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open scoped Classical in
open CompressionOWF CompressionLasVegas in
theorem solution (k s : ℕ) (hk : 1 ≤ k) :
    (∀ y ∈ bitStrings (k + s), (goodSeeds (prefixSeeded (j := k) (i := 0)) s y).Nonempty) ∧
    (∀ (R : Type) (_ : Fintype R) (D : R → Str → Str), Fintype.card R ≤ 2 ^ (k - 1) →
      ∃ y ∈ bitStrings (k + s), goodSeeds D s y = ∅) := by
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
  refine ⟨fun y hy => ?_, ?_⟩
  · have := hpre (i := 0) y (hbmem y hy)
    rw [pow_zero] at this
    exact Finset.card_pos.mp this
  · intro R _ D hR
    have hsum : ∑ y ∈ bitStrings (k + s), (goodSeeds D s y).card ≤ Fintype.card R * (2 ^ (s + 1) - 1) := by
      have hpos : ∀ p : Str, 1 ≤ natCode p := by
        intro p
        induction p with
        | nil => simp [natCode]
        | cons b t ih => simp only [natCode]; omega
      have hlt : ∀ p : Str, natCode p < 2 ^ (p.length + 1) := by
        intro p
        induction p with
        | nil => simp [natCode]
        | cons b t ih =>
          simp only [natCode, List.length_cons, pow_succ]
          split_ifs <;> omega
      have hinj : ∀ p q : Str, natCode p = natCode q → p = q := by
        intro p
        induction p with
        | nil =>
          intro q hq
          cases q with
          | nil => rfl
          | cons b t =>
            have := hpos t
            simp only [natCode] at hq
            split_ifs at hq <;> omega
        | cons b t ih =>
          intro q hq
          cases q with
          | nil =>
            have := hpos t
            simp only [natCode] at hq
            split_ifs at hq <;> omega
          | cons b' t' =>
            simp only [natCode] at hq
            have hbt : b = b' ∧ natCode t = natCode t' := by
              cases b <;> cases b' <;> simp at hq ⊢ <;> omega
            rw [hbt.1, ih t' hbt.2]
      have hcount : ∀ (D : Str → Str) (T : Finset Str),
          (∀ y ∈ T, Describable D y ∧ K D y ≤ s) → T.card ≤ 2 ^ (s + 1) - 1 := by
        intro D T hT
        have hshort : ∀ (y : Str), Describable D y → ∃ p : Str, p.length = K D y ∧ D p = y := by
          intro y hy
          obtain ⟨p₀, hp₀⟩ := hy
          exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ D p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
        classical
        let prog : Str → Str := fun y => if h : Describable D y then Classical.choose (hshort y h) else []
        have hprog : ∀ y ∈ T, (prog y).length = K D y ∧ D (prog y) = y := by
          intro y hy
          have hd := (hT y hy).1
          simp only [prog, dif_pos hd]
          exact Classical.choose_spec (hshort y hd)
        have hmaps : ∀ y ∈ T, natCode (prog y) ∈ Finset.Icc 1 (2 ^ (s + 1) - 1) := by
          intro y hy
          rw [Finset.mem_Icc]
          refine ⟨hpos _, ?_⟩
          have h1 := hlt (prog y)
          have h2 : 2 ^ ((prog y).length + 1) ≤ 2 ^ (s + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by rw [(hprog y hy).1]; have := (hT y hy).2; omega)
          omega
        have hinjOn : Set.InjOn (fun y => natCode (prog y)) T := by
          intro y₁ hy₁ y₂ hy₂ h
          have := hinj _ _ h
          rw [← (hprog y₁ hy₁).2, ← (hprog y₂ hy₂).2, this]
        have := Finset.card_le_card_of_injOn (fun y => natCode (prog y)) hmaps hinjOn
        simpa using this
      calc ∑ y ∈ bitStrings (k + s), (goodSeeds D s y).card
          = ∑ r, ((bitStrings (k + s)).filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s)).card := by
            unfold goodSeeds
            simp only [Finset.card_filter]
            exact Finset.sum_comm
        _ ≤ ∑ _r : R, (2 ^ (s + 1) - 1) :=
            Finset.sum_le_sum (fun r _ => hcount (D r) _ (fun y hy => (Finset.mem_filter.mp hy).2))
        _ = Fintype.card R * (2 ^ (s + 1) - 1) := by simp
    by_contra hall
    push Not at hall
    have hge : (bitStrings (k + s)).card ≤ ∑ y ∈ bitStrings (k + s), (goodSeeds D s y).card := by
      calc (bitStrings (k + s)).card = ∑ _y ∈ bitStrings (k + s), 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun y hy => Finset.card_pos.mpr (hall y hy))
    rw [hbcard] at hge
    have hp : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
    have h1 : Fintype.card R * (2 ^ (s + 1) - 1) ≤ 2 ^ (k - 1) * (2 ^ (s + 1) - 1) := Nat.mul_le_mul_right _ hR
    have h2 : 2 ^ (k - 1) * (2 ^ (s + 1) - 1) < 2 ^ (k - 1) * 2 ^ (s + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    have h3 : 2 ^ (k - 1) * 2 ^ (s + 1) = 2 ^ (k + s) := by
      rw [← pow_add]
      congr 1
      omega
    omega
