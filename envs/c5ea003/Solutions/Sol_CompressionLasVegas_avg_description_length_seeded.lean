-- Prove2me | solution 1 for CompressionLasVegas.avg_description_length_seeded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:29:53.813545+00:00
-- url     : https://prove2.me/submissions/6bfd1add-47ee-4458-a543-c6d5d5f756bd

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open scoped Classical in
open CompressionOWF CompressionLasVegas in
theorem solution {α : Type*} {R : Type*} [Fintype R] [DecidableEq R]
    (D : R → Str → α) (T : Finset α) (n k : ℕ) (hR : Fintype.card R ≤ 2 ^ k)
    (hdesc : ∀ y ∈ T, ∃ r : R, Describable (D r) y) (hT : 2 ^ n ≤ T.card) :
    (n - k - 3) * T.card ≤ ∑ y ∈ T, Kseed D y := by
  classical
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
  have hcount : ∀ (s : ℕ) (D : Str → α) (T : Finset α),
      (∀ y ∈ T, Describable D y ∧ K D y ≤ s) → T.card ≤ 2 ^ (s + 1) - 1 := by
    intro s D T hT
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
  have hlayer : ∀ (c : α → ℕ) (bnd : ℕ → ℕ) (S : ℕ),
      (∀ s < S, (T.filter (fun y => c y ≤ s)).card ≤ bnd s) →
      S * T.card ≤ (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, bnd s := by
    intro c bnd S h
    have hpt : ∀ y, S ≤ c y + ((Finset.range S).filter (fun s => c y ≤ s)).card := by
      intro y
      by_cases hy : S ≤ c y
      · omega
      · have heq : (Finset.range S).filter (fun s => c y ≤ s) = Finset.Ico (c y) S := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
        rw [heq, Nat.card_Ico]
        omega
    calc S * T.card = ∑ _y ∈ T, S := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ y ∈ T, (c y + ((Finset.range S).filter (fun s => c y ≤ s)).card) :=
          Finset.sum_le_sum (fun y _ => hpt y)
      _ = (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, (T.filter (fun y => c y ≤ s)).card := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ (∑ y ∈ T, c y) + ∑ s ∈ Finset.range S, bnd s := by
          gcongr with s hs
          exact h s (Finset.mem_range.mp hs)
  have hgeo : ∀ m, ∑ s ∈ Finset.range m, (2 ^ (s + 1) - 1) + 2 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (m + 1)]
      omega
  have hlev : ∀ s, (T.filter (fun y => Kseed D y ≤ s)).card ≤ 2 ^ k * (2 ^ (s + 1) - 1) := by
    intro s
    have hsub : T.filter (fun y => Kseed D y ≤ s)
        ⊆ Finset.univ.biUnion (fun r => T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s)) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨r0, p0, hp0⟩ := hdesc y hy.1
      obtain ⟨r, p, hpl, hpD⟩ := Nat.sInf_mem (s := {n | ∃ (r : R) (p : Str), p.length = n ∧ D r p = y})
        ⟨p0.length, r0, p0, rfl, hp0⟩
      have hKr : K (D r) y ≤ p.length := Nat.sInf_le ⟨p, rfl, hpD⟩
      have hks : Kseed D y = p.length := hpl.symm
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      exact ⟨r, hy.1, ⟨p, hpD⟩, by omega⟩
    calc (T.filter (fun y => Kseed D y ≤ s)).card
        ≤ (Finset.univ.biUnion (fun r => T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ r, (T.filter (fun y => Describable (D r) y ∧ K (D r) y ≤ s)).card := Finset.card_biUnion_le
      _ ≤ ∑ _r : R, (2 ^ (s + 1) - 1) :=
          Finset.sum_le_sum (fun r _ => hcount s (D r) _ (fun y hy => (Finset.mem_filter.mp hy).2))
      _ = Fintype.card R * (2 ^ (s + 1) - 1) := by simp
      _ ≤ 2 ^ k * (2 ^ (s + 1) - 1) := Nat.mul_le_mul_right _ hR
  rcases Nat.lt_or_ge n (k + 3) with hn | hn
  · have h0 : n - k - 3 = 0 := by omega
    simp [h0]
  · have h := hlayer (fun y => Kseed D y) (fun s => 2 ^ k * (2 ^ (s + 1) - 1)) (n - k - 2)
      (fun s _ => hlev s)
    simp only at h
    have hg := hgeo (n - k - 2)
    rw [← Finset.mul_sum] at h
    have hpow : 2 ^ k * 2 ^ (n - k - 2 + 1) ≤ 2 ^ n := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmul2 : 2 ^ k * (∑ s ∈ Finset.range (n - k - 2), (2 ^ (s + 1) - 1)) ≤ 2 ^ k * 2 ^ (n - k - 2 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul : (n - k - 2) * T.card = (n - k - 3) * T.card + T.card := by
      have h' : n - k - 2 = (n - k - 3) + 1 := by omega
      rw [h']
      ring
    omega
