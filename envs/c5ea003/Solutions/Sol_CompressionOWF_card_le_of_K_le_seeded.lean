-- Prove2me | solution 1 for CompressionOWF.card_le_of_K_le_seeded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:38:45.953332+00:00
-- url     : https://prove2.me/submissions/c1ca11ad-4d34-4845-89eb-97545e9b7427

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution {α : Type*} {R : Type*} [Fintype R] [DecidableEq R]
    (D : R → Str → α) (s : ℕ) (T : Finset α)
    (hT : ∀ y ∈ T, ∃ r : R, Describable (D r) y ∧ K (D r) y ≤ s) :
    T.card ≤ Fintype.card R * (2 ^ (s + 1) - 1) := by
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
  have hcount : ∀ (D : Str → α) (T : Finset α),
      (∀ y ∈ T, Describable D y ∧ K D y ≤ s) → T.card ≤ 2 ^ (s + 1) - 1 := by
    intro D T hT
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
  classical
  have hsub : T ⊆ Finset.univ.biUnion
      (fun r : R => T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s)) := by
    intro y hy
    obtain ⟨r, hr⟩ := hT y hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨r, hy, hr⟩
  calc T.card
      ≤ (Finset.univ.biUnion
          (fun r : R => T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r : R, (T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _r : R, (2 ^ (s + 1) - 1) :=
        Finset.sum_le_sum (fun r _ => hcount (D r) _ (fun y hy => (Finset.mem_filter.mp hy).2))
    _ = Fintype.card R * (2 ^ (s + 1) - 1) := by simp
