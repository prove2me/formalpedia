-- Prove2me | solution 2 for RelWalkCount.card_closedWalks_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:27:03.492373+00:00
-- url     : https://prove2.me/submissions/066fdef0-4b3a-4c09-b4d6-a9b51c677841

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open RelWalkCount Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop) [DecidableRel r]
    {q : ℕ} (hq : ∀ a : ι, ∑ b, relMatrix r a b = q) (n : ℕ) :
    (closedWalks r n).card ≤ Fintype.card ι * q ^ n := by
  -- entries of `A^n` count walks
  have hpow : ∀ (n : ℕ) (a b : ι), (relMatrix r ^ n) a b = (walks r n a b).card := by
    -- every walk starts at its source
    have hhead : ∀ (n : ℕ) (a b : ι) (l : List ι), l ∈ walks r n a b → l.head? = some a := by
      intro n a b l hl
      cases n with
      | zero =>
        simp only [walks] at hl
        split_ifs at hl with hab
        · rw [Finset.mem_singleton] at hl
          rw [hl]
          rfl
        · simp at hl
      | succ n =>
        simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
        obtain ⟨c, -, l', -, rfl⟩ := hl
        rfl
    intro n
    induction n with
    | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      simp only [walks]
      split_ifs <;> simp
    | succ n ih =>
      intro a b
      rw [pow_succ', Matrix.mul_apply]
      simp only [walks]
      -- the images for different second vertices are disjoint
      rw [Finset.card_biUnion]
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ih c b, Finset.card_image_of_injective _ (List.cons_injective)]
        simp only [relMatrix, Matrix.of_apply]
        split_ifs <;> simp
      · intro c _ c' _ hcc'
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro l hl hl'
        rw [Finset.mem_image] at hl hl'
        obtain ⟨l₁, h₁, rfl⟩ := hl
        obtain ⟨l₂, h₂, heq⟩ := hl'
        have h12 : l₂ = l₁ := List.cons_injective heq
        subst h12
        have e1 := hhead n c b _ h₁
        have e2 := hhead n c' b _ h₂
        rw [e1] at e2
        exact hcc' (Option.some_injective _ e2)
  -- row sums of `A^n` are `q^n`
  have hrow : ∀ (n : ℕ) (a : ι), ∑ b, (relMatrix r ^ n) a b = q ^ n := by
    intro n
    induction n with
    | zero =>
      intro a
      simp [Matrix.one_apply]
    | succ n ih =>
      intro a
      simp only [pow_succ', Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, ih, ← Finset.sum_mul, hq]
  calc (closedWalks r n).card ≤ ∑ a, (walks r n a a).card := by
        unfold closedWalks
        exact Finset.card_biUnion_le
    _ = ∑ a, (relMatrix r ^ n) a a := by simp only [hpow]
    _ ≤ ∑ a, ∑ b, (relMatrix r ^ n) a b := Finset.sum_le_sum fun a _ =>
        Finset.single_le_sum (f := fun b => (relMatrix r ^ n) a b) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ a)
    _ = Fintype.card ι * q ^ n := by simp [hrow]
