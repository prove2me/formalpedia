-- Prove2me | solution 1 for CompressionOWF.card_le_of_K_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:32:44.890272+00:00
-- url     : https://prove2.me/submissions/2c1114ec-f9f3-48fc-8130-a7cc58beeff1

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution {α : Type*} (D : Str → α) (s : ℕ) (T : Finset α)
    (hT : ∀ y ∈ T, Describable D y ∧ K D y ≤ s) : T.card ≤ 2 ^ (s + 1) - 1 := by
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
  have hshort : ∀ (y : α), Describable D y → ∃ p : Str, p.length = K D y ∧ D p = y := by
    intro y hy
    obtain ⟨p₀, hp₀⟩ := hy
    exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ D p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
  classical
  let prog : α → Str := fun y => if h : Describable D y then Classical.choose (hshort y h) else []
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
