-- Prove2me | solution 2 for CompressionOWF.density_incompressible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:27:31.058929+00:00
-- url     : https://prove2.me/submissions/96050499-6b34-4a9c-b97f-7c9d9690059b

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
open scoped Classical in
open CompressionOWF in
theorem solution (D : Str → Str) (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    2 ^ (c - 1) *
        ((bitStrings n).filter (fun y => Describable D y ∧ K D y ≤ n - c)).card
      ≤ (bitStrings n).card := by
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
  have hshort : ∀ {β : Type} (D : Str → β) (y : β), Describable D y →
      ∃ p : Str, p.length = K D y ∧ D p = y := by
    intro β D y hy
    obtain ⟨p₀, hp₀⟩ := hy
    exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ D p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
  have hcount : ∀ {β : Type} (D : Str → β) (s : ℕ) (T : Finset β),
      (∀ y ∈ T, Describable D y ∧ K D y ≤ s) → T.card ≤ 2 ^ (s + 1) - 1 := by
    intro β D s T hT
    classical
    let prog : β → Str := fun y => if h : Describable D y then Classical.choose (hshort D y h) else []
    have hprog : ∀ y ∈ T, (prog y).length = K D y ∧ D (prog y) = y := by
      intro y hy
      have hd := (hT y hy).1
      simp only [prog, dif_pos hd]
      exact Classical.choose_spec (hshort D y hd)
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
  have hF : ((bitStrings n).filter (fun y => Describable D y ∧ K D y ≤ n - c)).card
      ≤ 2 ^ (n - c + 1) - 1 :=
    hcount D (n - c) _ (fun y hy => (Finset.mem_filter.mp hy).2)
  have hB : (bitStrings n).card = 2 ^ n := by
    unfold bitStrings
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  rw [hB]
  have hexp : 2 ^ (c - 1) * 2 ^ (n - c + 1) = 2 ^ n := by
    rw [← pow_add]
    congr 1
    omega
  calc 2 ^ (c - 1) * ((bitStrings n).filter (fun y => Describable D y ∧ K D y ≤ n - c)).card
      ≤ 2 ^ (c - 1) * (2 ^ (n - c + 1) - 1) := Nat.mul_le_mul_left _ hF
    _ ≤ 2 ^ (c - 1) * 2 ^ (n - c + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 2 ^ n := hexp
