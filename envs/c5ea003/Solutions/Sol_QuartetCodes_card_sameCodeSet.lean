-- Prove2me | solution 1 for QuartetCodes.card_sameCodeSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:45:18.338629+00:00
-- url     : https://prove2.me/submissions/a4c86079-9739-4958-a5cf-f2868ca871e3

import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes

open QuartetCodes Finset in
theorem solution {n k : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (i₀ : Fin k) :
    (sameCodeSet i₀ a b c d).card = 3 * (qclass a b c d 0).card ^ k := by
  -- `code3` reads off which of the three pairings is separated
  have hA : ∀ P Q R S : ℕ, ((P < R ∧ P < S) ∧ (Q < R ∧ Q < S) ∨
      (R < P ∧ R < Q) ∧ (S < P ∧ S < Q)) → code3 P Q R S = 0 := by
    intro P Q R S h
    unfold code3
    simp only [max_lt_iff, lt_min_iff]
    split_ifs <;> first | (exfalso; omega) | rfl
  have hB : ∀ P Q R S : ℕ, ((P < Q ∧ P < S) ∧ (R < Q ∧ R < S) ∨
      (Q < P ∧ Q < R) ∧ (S < P ∧ S < R)) → code3 P Q R S = 1 := by
    intro P Q R S h
    unfold code3
    simp only [max_lt_iff, lt_min_iff]
    split_ifs <;> first | (exfalso; omega) | rfl
  have hC : ∀ P Q R S : ℕ, ((P < Q ∧ P < R) ∧ (S < Q ∧ S < R) ∨
      (Q < P ∧ Q < S) ∧ (R < P ∧ R < S)) → code3 P Q R S = 2 := by
    intro P Q R S h
    unfold code3
    simp only [max_lt_iff, lt_min_iff]
    split_ifs <;> first | (exfalso; omega) | rfl
  -- four distinct values: one of the three pairings is separated
  have hABC : ∀ P Q R S : ℕ, P ≠ Q → P ≠ R → P ≠ S → Q ≠ R → Q ≠ S → R ≠ S →
      ((P < R ∧ P < S) ∧ (Q < R ∧ Q < S) ∨ (R < P ∧ R < Q) ∧ (S < P ∧ S < Q)) ∨
      ((P < Q ∧ P < S) ∧ (R < Q ∧ R < S) ∨ (Q < P ∧ Q < R) ∧ (S < P ∧ S < R)) ∨
      ((P < Q ∧ P < R) ∧ (S < Q ∧ S < R) ∨ (Q < P ∧ Q < S) ∧ (R < P ∧ R < S)) := by
    intro P Q R S h1 h2 h3 h4 h5 h6
    rcases Nat.lt_or_gt_of_ne h1 with a1 | a1 <;> rcases Nat.lt_or_gt_of_ne h2 with a2 | a2 <;>
    rcases Nat.lt_or_gt_of_ne h3 with a3 | a3 <;> rcases Nat.lt_or_gt_of_ne h4 with a4 | a4 <;>
    rcases Nat.lt_or_gt_of_ne h5 with a5 | a5 <;> rcases Nat.lt_or_gt_of_ne h6 with a6 | a6
    all_goals first
      | exact Or.inl (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)
      | exact Or.inl (Or.inr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)
      | exact Or.inr (Or.inl (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
      | exact Or.inr (Or.inl (Or.inr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩))
      | (exfalso; omega)
  -- swapping two positions permutes the three quartet types
  have hc01 : ∀ P Q R S : ℕ, P ≠ Q → P ≠ R → P ≠ S → Q ≠ R → Q ≠ S → R ≠ S →
      code3 P R Q S = ![1, 0, 2] (code3 P Q R S) := by
    intro P Q R S h1 h2 h3 h4 h5 h6
    rcases hABC P Q R S h1 h2 h3 h4 h5 h6 with h | h | h
    · rw [hA P Q R S h, hB P R Q S (by omega)]
      rfl
    · rw [hB P Q R S h, hA P R Q S (by omega)]
      rfl
    · rw [hC P Q R S h, hC P R Q S (by omega)]
      rfl
  have hc02 : ∀ P Q R S : ℕ, P ≠ Q → P ≠ R → P ≠ S → Q ≠ R → Q ≠ S → R ≠ S →
      code3 P S R Q = ![2, 1, 0] (code3 P Q R S) := by
    intro P Q R S h1 h2 h3 h4 h5 h6
    rcases hABC P Q R S h1 h2 h3 h4 h5 h6 with h | h | h
    · rw [hA P Q R S h, hC P S R Q (by omega)]
      rfl
    · rw [hB P Q R S h, hB P S R Q (by omega)]
      rfl
    · rw [hC P Q R S h, hA P S R Q (by omega)]
      rfl
  have hv : ∀ π : Equiv.Perm (Fin n), ∀ x y : Fin n, x ≠ y → (π x).val ≠ (π y).val :=
    fun π x y h hxy => h (π.injective (Fin.ext hxy))
  have hp1 : ∀ π : Equiv.Perm (Fin n),
      qcode (π * Equiv.swap b c) a b c d = ![1, 0, 2] (qcode π a b c d) := by
    intro π
    simp only [qcode, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm]
    exact hc01 _ _ _ _ (hv π a b hab) (hv π a c hac) (hv π a d had) (hv π b c hbc)
      (hv π b d hbd) (hv π c d hcd)
  have hp2 : ∀ π : Equiv.Perm (Fin n),
      qcode (π * Equiv.swap b d) a b c d = ![2, 1, 0] (qcode π a b c d) := by
    intro π
    simp only [qcode, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_of_ne_of_ne hbc.symm hcd]
    exact hc02 _ _ _ _ (hv π a b hab) (hv π a c hac) (hv π a d had) (hv π b c hbc)
      (hv π b d hbd) (hv π c d hcd)
  have hmem : ∀ (π : Equiv.Perm (Fin n)) (t : Fin 3), π ∈ qclass a b c d t ↔ qcode π a b c d = t := by
    intro π t
    simp [qclass]
  -- so the three classes have the same size
  have hcard : ∀ (x y : Fin n) (τ : Fin 3 → Fin 3), (∀ t, τ (τ t) = t) →
      (∀ π : Equiv.Perm (Fin n), qcode (π * Equiv.swap x y) a b c d = τ (qcode π a b c d)) →
      ∀ t, (qclass a b c d (τ t)).card = (qclass a b c d t).card := by
    intro x y τ hτ hq t
    symm
    apply Finset.card_nbij' (fun π => π * Equiv.swap x y) (fun π => π * Equiv.swap x y)
    · intro π hπ
      simp only [Finset.mem_coe, hmem] at hπ ⊢
      rw [hq, hπ]
    · intro π hπ
      simp only [Finset.mem_coe, hmem] at hπ ⊢
      rw [hq, hπ, hτ]
    · intro π _
      simp [mul_assoc]
    · intro π _
      simp [mul_assoc]
  have e1 : (qclass a b c d 1).card = (qclass a b c d 0).card :=
    hcard b c ![1, 0, 2] (by decide) hp1 0
  have e2 : (qclass a b c d 2).card = (qclass a b c d 0).card :=
    hcard b d ![2, 1, 0] (by decide) hp2 0
  -- families showing one common type split by that type into three product sets
  have hsplit : sameCodeSet i₀ a b c d = (univ : Finset (Fin 3)).biUnion
      (fun t => Fintype.piFinset (fun _ : Fin k => qclass a b c d t)) := by
    ext T
    simp only [sameCodeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Fintype.mem_piFinset, hmem]
    constructor
    · intro h
      exact ⟨qcode (T i₀) a b c d, fun i => h i⟩
    · rintro ⟨t, ht⟩ i
      rw [ht i, ht i₀]
  have hdisj : ∀ t ∈ (univ : Finset (Fin 3)), ∀ t' ∈ (univ : Finset (Fin 3)), t ≠ t' →
      Disjoint (Fintype.piFinset (fun _ : Fin k => qclass a b c d t))
        (Fintype.piFinset (fun _ : Fin k => qclass a b c d t')) := by
    intro t _ t' _ htt
    rw [Finset.disjoint_left]
    intro T h1 h2
    rw [Fintype.mem_piFinset] at h1 h2
    have f1 := (hmem _ _).1 (h1 i₀)
    have f2 := (hmem _ _).1 (h2 i₀)
    exact htt (f1.symm.trans f2)
  rw [hsplit, Finset.card_biUnion hdisj]
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Fin.sum_univ_three, e1, e2]
  ring
