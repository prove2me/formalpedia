-- Prove2me | solution 1 for CRTSplitNoGo.card_injPrefix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:52:50.116984+00:00
-- url     : https://prove2.me/submissions/404bd194-803c-4951-a71f-bf9f4b5a93b8

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday

open CRTSplitNoGo Finset in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (a : α) (T : ℕ)
    (hT : T < Fintype.card α) :
    (injPrefixFinset a T).card
      = (Fintype.card α - 1).descFactorial T * (Fintype.card α) ^ (Fintype.card α - T) := by
  classical
  have horb_succ : ∀ (f : α → α) (i : ℕ), orb f a (i + 1) = f (orb f a i) := by
    intro f i
    simp only [orb, Function.iterate_succ_apply']
  have hmem : ∀ (f : α → α) (S : ℕ), f ∈ injPrefixFinset a S ↔ InjPrefix f a S := by
    intro f S
    simp [injPrefixFinset]
  -- updating `f` at the last prefix point does not move the prefix
  have hL1 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v, ∀ i ≤ S,
      orb (Function.update f (orb f a S) v) a i = orb f a i := by
    intro f S hf v i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [horb_succ, horb_succ, ih (by omega), Function.update_of_ne]
      intro h
      have := hf i (by omega) S le_rfl h
      omega
  have hL2 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      InjPrefix (Function.update f (orb f a S) v) a S := by
    intro f S hf v i hi j hj h
    rw [hL1 f S hf v i hi, hL1 f S hf v j hj] at h
    exact hf i hi j hj h
  have hlast : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      orb (Function.update f (orb f a S) v) a (S + 1) = v := by
    intro f S hf v
    rw [horb_succ, hL1 f S hf v S le_rfl, Function.update_self]
  have hL3 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      InjPrefix (Function.update f (orb f a S) v) a (S + 1) ↔ ∀ i ≤ S, v ≠ orb f a i := by
    intro f S hf v
    constructor
    · intro h i hi hv
      have h1 := hlast f S hf v
      have h2 := hL1 f S hf v i hi
      have := h (S + 1) le_rfl i (by omega) (by rw [h1, h2, hv])
      omega
    · intro hv i hi j hj h
      rcases Nat.lt_or_ge i (S + 1) with hi' | hi' <;>
        rcases Nat.lt_or_ge j (S + 1) with hj' | hj'
      · exact hL2 f S hf v i (by omega) j (by omega) h
      · have hjS : j = S + 1 := by omega
        subst hjS
        rw [hlast f S hf v, hL1 f S hf v i (by omega)] at h
        exact absurd h.symm (hv i (by omega))
      · have hiS : i = S + 1 := by omega
        subst hiS
        rw [hlast f S hf v, hL1 f S hf v j (by omega)] at h
        exact absurd h (hv j (by omega))
      · omega
  have hreset : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      reset a S (Function.update f (orb f a S) v) = reset a S f := by
    intro f S hf v
    unfold reset
    rw [hL1 f S hf v S le_rfl, Function.update_idem]
  have hL5 : ∀ (f f' : α → α) (S : ℕ), InjPrefix f a S → InjPrefix f' a S →
      reset a S f = reset a S f' → f' = Function.update f (orb f a S) (f' (orb f a S)) := by
    intro f f' S hf hf' h
    have hx : orb f a S = orb f' a S := by
      have e1 := hL1 f S hf a S le_rfl
      have e2 := hL1 f' S hf' a S le_rfl
      unfold reset at h
      rw [← e1, ← e2, h]
    funext y
    by_cases hy : y = orb f a S
    · subst hy
      rw [Function.update_self]
    · rw [Function.update_of_ne hy]
      have h1 := congrFun h y
      unfold reset at h1
      rw [Function.update_of_ne hy, Function.update_of_ne (hx ▸ hy)] at h1
      exact h1.symm
  -- the recursion `|S(T+1)| · N = |S(T)| · (N - (T+1))`
  have hstep : ∀ S : ℕ, S + 1 < Fintype.card α →
      (injPrefixFinset a (S + 1)).card * Fintype.card α
        = (injPrefixFinset a S).card * (Fintype.card α - (S + 1)) := by
    intro S hS
    set t := (injPrefixFinset a S).image (reset a S) with ht
    have hsub : injPrefixFinset a (S + 1) ⊆ injPrefixFinset a S := by
      intro f hf
      rw [hmem] at hf ⊢
      exact fun i hi j hj h => hf i (by omega) j (by omega) h
    -- fibre sizes over each `h ∈ t`
    have hfibT : ∀ h ∈ t, ((injPrefixFinset a S).filter (fun f => reset a S f = h)).card
        = Fintype.card α := by
      intro h hh
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hh
      rw [hmem] at hf0
      have heq : (injPrefixFinset a S).filter (fun f => reset a S f = reset a S f0)
          = univ.image (fun v => Function.update f0 (orb f0 a S) v) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hmem]
        constructor
        · rintro ⟨hg, hgr⟩
          exact ⟨g (orb f0 a S), (hL5 f0 g S hf0 hg hgr.symm).symm⟩
        · rintro ⟨v, rfl⟩
          exact ⟨hL2 f0 S hf0 v, hreset f0 S hf0 v⟩
      rw [heq, Finset.card_image_of_injective, Finset.card_univ]
      intro v w hvw
      have := congrFun hvw (orb f0 a S)
      simpa using this
    have hfibT1 : ∀ h ∈ t, ((injPrefixFinset a (S + 1)).filter (fun f => reset a S f = h)).card
        = Fintype.card α - (S + 1) := by
      intro h hh
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hh
      rw [hmem] at hf0
      have heq : (injPrefixFinset a (S + 1)).filter (fun f => reset a S f = reset a S f0)
          = (univ.filter (fun v => ∀ i ≤ S, v ≠ orb f0 a i)).image
              (fun v => Function.update f0 (orb f0 a S) v) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hmem]
        constructor
        · rintro ⟨hg, hgr⟩
          have hgS : InjPrefix g a S := fun i hi j hj h => hg i (by omega) j (by omega) h
          have hgeq := hL5 f0 g S hf0 hgS hgr.symm
          refine ⟨g (orb f0 a S), ?_, hgeq.symm⟩
          rw [hgeq] at hg
          exact (hL3 f0 S hf0 _).1 hg
        · rintro ⟨v, hv, rfl⟩
          exact ⟨(hL3 f0 S hf0 v).2 hv, hreset f0 S hf0 v⟩
      rw [heq, Finset.card_image_of_injective]
      · have hcompl : univ.filter (fun v => ∀ i ≤ S, v ≠ orb f0 a i)
            = univ \ (range (S + 1)).image (orb f0 a) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
            Finset.mem_image, Finset.mem_range, not_exists, not_and]
          constructor
          · intro h i hi hv
            exact h i (by omega) hv.symm
          · intro h i hi hv
            exact h i (by omega) hv.symm
        rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Finset.card_image_of_injOn, Finset.card_range]
        intro i hi j hj h
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        exact hf0 i (by omega) j (by omega) h
      · intro v w hvw
        have := congrFun hvw (orb f0 a S)
        simpa using this
    have hA := Finset.card_eq_sum_card_fiberwise (f := reset a S) (s := injPrefixFinset a S)
      (t := t) (fun f hf => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hf))
    have hB := Finset.card_eq_sum_card_fiberwise (f := reset a S)
      (s := injPrefixFinset a (S + 1)) (t := t)
      (fun f hf => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hsub hf)))
    rw [Finset.sum_congr rfl hfibT, Finset.sum_const, smul_eq_mul] at hA
    rw [Finset.sum_congr rfl hfibT1, Finset.sum_const, smul_eq_mul] at hB
    rw [hA, hB]
    ring
  -- closed form by induction on the prefix length
  have hmain : ∀ S : ℕ, S < Fintype.card α → (injPrefixFinset a S).card
      = (Fintype.card α - 1).descFactorial S * (Fintype.card α) ^ (Fintype.card α - S) := by
    intro S
    induction S with
    | zero =>
      intro _
      have huniv : injPrefixFinset a 0 = univ := by
        ext f
        simp only [Finset.mem_univ, iff_true, hmem]
        intro i hi j hj _
        omega
      rw [huniv, Finset.card_univ, Fintype.card_fun, Nat.descFactorial_zero, one_mul,
        Nat.sub_zero]
    | succ S ih =>
      intro hS
      have hN : 0 < Fintype.card α := by omega
      have h1 := hstep S hS
      rw [ih (by omega)] at h1
      apply Nat.eq_of_mul_eq_mul_right hN
      rw [h1, Nat.descFactorial_succ]
      have e : Fintype.card α - S = (Fintype.card α - (S + 1)) + 1 := by omega
      rw [e, pow_succ]
      have e2 : Fintype.card α - 1 - S = Fintype.card α - (S + 1) := by omega
      rw [e2]
      ring
  exact hmain T hT
