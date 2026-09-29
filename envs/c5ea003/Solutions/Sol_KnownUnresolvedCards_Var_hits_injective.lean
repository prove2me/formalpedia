-- Prove2me | solution 1 for KnownUnresolvedCards.Var_hits_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:25:42.820891+00:00
-- url     : https://prove2.me/submissions/71b35137-6966-4c65-9843-0b7ee1138b86

import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount

set_option maxHeartbeats 1000000 in
open Finset KnownUnresolvedCards in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (hcard : 2 ≤ Fintype.card α)
    {g : α → α} (hg : Function.Injective g) :
    Var (fun σ : Equiv.Perm α => (hits g σ : ℚ)) = 1 := by
  classical
  have hcore : ∀ g : α → α,
      Fintype.card α * (Fintype.card α - 1) * (∑ σ : Equiv.Perm α, (hits g σ) ^ 2)
        = (Fintype.card α * (Fintype.card α - 1) + distinctCallPairs g)
            * Fintype.card (Equiv.Perm α) := by
    intro g
    set N : ℕ := Fintype.card α with hNdef
    set P : ℕ := Fintype.card (Equiv.Perm α) with hPdef
    -- the fibre of `σ ↦ σ i` over `a`, and its refinement by the value at `j`
    set fib : α → α → ℕ := fun i a => (univ.filter (fun σ : Equiv.Perm α => σ i = a)).card
      with hfibdef
    set pf : α → α → α → α → ℕ :=
      fun i j a b => (univ.filter (fun σ : Equiv.Perm α => σ i = a ∧ σ j = b)).card with hpfdef
    -- all fibres over the same slot have the same size
    have hfibeq : ∀ (i x y : α), fib i x = fib i y := by
      intro i x y
      rw [hfibdef]
      refine Finset.card_bij' (fun σ _ => Equiv.swap x y * σ) (fun σ _ => Equiv.swap x y * σ)
        ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        simp [Equiv.Perm.mul_apply, hσ]
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        simp [Equiv.Perm.mul_apply, hσ]
      · intro σ _
        simp [← mul_assoc]
      · intro σ _
        simp [← mul_assoc]
    -- `|α|` copies of a fibre make up the whole group
    have hfibN : ∀ (i a : α), N * fib i a = P := by
      intro i a
      have hpart : (univ : Finset (Equiv.Perm α)).card
          = ∑ x ∈ (univ : Finset α), (univ.filter (fun σ : Equiv.Perm α => σ i = x)).card :=
        Finset.card_eq_sum_card_fiberwise (fun σ _ => Finset.mem_univ (σ i))
      rw [Finset.card_univ] at hpart
      have hsum : ∑ x ∈ (univ : Finset α), fib i x = N * fib i a := by
        rw [Finset.sum_congr rfl (fun x _ => hfibeq i x a), Finset.sum_const, Finset.card_univ,
          smul_eq_mul, hNdef]
      rw [hPdef, hpart, ← hsum]
    -- two distinct slots never take the same value
    have hpz : ∀ (i j a : α), i ≠ j → pf i j a a = 0 := by
      intro i j a hij
      rw [hpfdef, Finset.card_eq_zero]
      refine Finset.eq_empty_of_forall_notMem ?_
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact hij (σ.injective (hσ.1.trans hσ.2.symm))
    -- the refined fibres over a fixed first value all have the same size
    have hpfeq : ∀ (i j a b c : α), b ≠ a → c ≠ a → pf i j a b = pf i j a c := by
      intro i j a b c hb hc
      rw [hpfdef]
      refine Finset.card_bij' (fun σ _ => Equiv.swap b c * σ) (fun σ _ => Equiv.swap b c * σ)
        ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        exact ⟨by rw [Equiv.Perm.mul_apply, hσ.1, Equiv.swap_apply_of_ne_of_ne hb.symm hc.symm],
          by rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]⟩
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        exact ⟨by rw [Equiv.Perm.mul_apply, hσ.1, Equiv.swap_apply_of_ne_of_ne hb.symm hc.symm],
          by rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_right]⟩
      · intro σ _
        simp [← mul_assoc]
      · intro σ _
        simp [← mul_assoc]
    -- splitting a fibre by the value at a second slot
    have hsplit : ∀ (i j a : α), fib i a = ∑ b ∈ (univ : Finset α), pf i j a b := by
      intro i j a
      simp only [hfibdef, hpfdef]
      have hpart := Finset.card_eq_sum_card_fiberwise
        (f := fun σ : Equiv.Perm α => σ j) (s := univ.filter (fun σ : Equiv.Perm α => σ i = a))
        (t := (univ : Finset α)) (fun σ _ => Finset.mem_univ (σ j))
      rw [hpart]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      congr 1
      rw [Finset.filter_filter]
    have hpfN : ∀ (i j a b : α), i ≠ j → b ≠ a → (N - 1) * pf i j a b = fib i a := by
      intro i j a b hij hb
      have hz := hpz i j a hij
      have hsum := hsplit i j a
      have herase : ∑ x ∈ (univ : Finset α).erase a, pf i j a x + pf i j a a
          = ∑ x ∈ (univ : Finset α), pf i j a x := Finset.sum_erase_add _ _ (Finset.mem_univ a)
      have hcong : ∑ x ∈ (univ : Finset α).erase a, pf i j a x
          = ((univ : Finset α).erase a).card * pf i j a b := by
        rw [Finset.sum_congr rfl (fun x hx => hpfeq i j a x b (Finset.ne_of_mem_erase hx) hb),
          Finset.sum_const, smul_eq_mul]
      have hcard : ((univ : Finset α).erase a).card = N - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hNdef]
      rw [hcard] at hcong
      rw [hsum, ← herase, hz, Nat.add_zero, hcong]
    -- the square of the score counts ordered pairs of correctly named slots
    have hsq : ∑ σ : Equiv.Perm α, (hits g σ) ^ 2 = ∑ i, ∑ j, pf i j (g i) (g j) := by
      have hpt : ∀ σ : Equiv.Perm α, (hits g σ) ^ 2
          = ∑ i, ∑ j, (if σ i = g i ∧ σ j = g j then 1 else 0) := by
        intro σ
        have hh : hits g σ = ∑ i, (if σ i = g i then 1 else 0) := by
          rw [hits, Finset.card_filter]
        rw [hh, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        by_cases h1 : σ i = g i <;> by_cases h2 : σ j = g j <;> simp [h1, h2]
      rw [Finset.sum_congr rfl (fun σ _ => hpt σ)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hpfdef]
      rw [Finset.card_filter]
    -- the key per-term identity
    have hterm : ∀ i j : α, N * (N - 1) * pf i j (g i) (g j)
        = (if j = i then (N - 1) * P else 0) + (if g i ≠ g j then P else 0) := by
      intro i j
      by_cases hji : j = i
      · subst hji
        have hself : pf j j (g j) (g j) = fib j (g j) := by
          simp only [hpfdef, hfibdef, and_self]
        rw [hself, if_pos rfl, if_neg (by simp), Nat.add_zero]
        calc N * (N - 1) * fib j (g j) = (N - 1) * (N * fib j (g j)) := by ring
          _ = (N - 1) * P := by rw [hfibN]
      · by_cases hg : g i = g j
        · have hz : pf i j (g i) (g j) = 0 := by
            rw [← hg]
            exact hpz i j (g i) (fun h => hji h.symm)
          rw [hz, if_neg hji, if_neg (by simp [hg]), Nat.mul_zero]
        · have hb : g j ≠ g i := fun h => hg h.symm
          have hkey := hpfN i j (g i) (g j) (fun h => hji h.symm) hb
          rw [if_neg hji, if_pos hg, Nat.zero_add]
          calc N * (N - 1) * pf i j (g i) (g j) = N * ((N - 1) * pf i j (g i) (g j)) := by ring
            _ = N * fib i (g i) := by rw [hkey]
            _ = P := hfibN i (g i)
    -- assemble
    have hrow : ∀ i : α, ∑ j, N * (N - 1) * pf i j (g i) (g j)
        = (N - 1) * P + distinctCalls g i * P := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ => hterm i j), Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_ite_eq' (univ : Finset α) i (fun _ => (N - 1) * P), if_pos (Finset.mem_univ i)]
      · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
          Nat.mul_zero, Nat.add_zero, distinctCalls]
    calc N * (N - 1) * (∑ σ : Equiv.Perm α, (hits g σ) ^ 2)
        = ∑ i, ∑ j, N * (N - 1) * pf i j (g i) (g j) := by
          rw [hsq, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ i : α, ((N - 1) * P + distinctCalls g i * P) :=
          Finset.sum_congr rfl (fun i _ => hrow i)
      _ = N * ((N - 1) * P) + (∑ i, distinctCalls g i) * P := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hNdef,
            ← Finset.sum_mul]
      _ = (N * (N - 1) + distinctCallPairs g) * P := by
          rw [distinctCallPairs]
          ring

  -- the expected number of hits is always exactly one
  have hsum1 : ∀ g : α → α, ∑ σ : Equiv.Perm α, hits g σ = Fintype.card (Equiv.Perm α) := by
    intro g
    have hfibeq : ∀ (i x y : α),
        (univ.filter (fun σ : Equiv.Perm α => σ i = x)).card
          = (univ.filter (fun σ : Equiv.Perm α => σ i = y)).card := by
      intro i x y
      refine Finset.card_bij' (fun σ _ => Equiv.swap x y * σ) (fun σ _ => Equiv.swap x y * σ)
        ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        simp [Equiv.Perm.mul_apply, hσ]
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        simp [Equiv.Perm.mul_apply, hσ]
      · intro σ _
        simp [← mul_assoc]
      · intro σ _
        simp [← mul_assoc]
    have hfibN : ∀ (i a : α),
        Fintype.card α * (univ.filter (fun σ : Equiv.Perm α => σ i = a)).card
          = Fintype.card (Equiv.Perm α) := by
      intro i a
      have hpart : (univ : Finset (Equiv.Perm α)).card
          = ∑ x ∈ (univ : Finset α), (univ.filter (fun σ : Equiv.Perm α => σ i = x)).card :=
        Finset.card_eq_sum_card_fiberwise (fun σ _ => Finset.mem_univ (σ i))
      rw [Finset.card_univ] at hpart
      rw [hpart, Finset.sum_congr rfl (fun x _ => hfibeq i x a), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
    have hexp : ∑ σ : Equiv.Perm α, hits g σ
        = ∑ i, (univ.filter (fun σ : Equiv.Perm α => σ i = g i)).card := by
      have hh : ∀ σ : Equiv.Perm α, hits g σ = ∑ i, (if σ i = g i then 1 else 0) := by
        intro σ
        rw [hits, Finset.card_filter]
      rw [Finset.sum_congr rfl (fun σ _ => hh σ), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.card_filter]
    have hNpos : 0 < Fintype.card α := by omega
    refine Nat.eq_of_mul_eq_mul_left hNpos ?_
    rw [hexp, Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hfibN i (g i)),
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m + 2 := ⟨Fintype.card α - 2, by omega⟩
  have hsub : Fintype.card α - 1 = m + 1 := by omega
  have hPne : ((Fintype.card (Equiv.Perm α) : ℕ) : ℚ) ≠ 0 := by
    have : 0 < Fintype.card (Equiv.Perm α) := Fintype.card_pos
    positivity
  have hcastsum : ∀ g : α → α, ∑ σ : Equiv.Perm α, ((hits g σ : ℚ))
      = ((Fintype.card (Equiv.Perm α) : ℕ) : ℚ) := by
    intro g
    rw [← Nat.cast_sum, hsum1 g]
  have hcastsq : ∀ g : α → α, ∑ σ : Equiv.Perm α, ((hits g σ : ℚ)) ^ 2
      = ((∑ σ : Equiv.Perm α, (hits g σ) ^ 2 : ℕ) : ℚ) := by
    intro g
    push_cast
    rfl
  -- an injective strategy makes every ordered pair of distinct slots a distinct pair of calls
  have hD : distinctCallPairs g = Fintype.card α * (Fintype.card α - 1) := by
    have hcalls : ∀ i : α, distinctCalls g i = Fintype.card α - 1 := by
      intro i
      have hset : (univ.filter (fun j => g i ≠ g j)) = (univ : Finset α).erase i := by
        ext j
        rw [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨-, h⟩
          exact ⟨fun hj => h (by rw [hj]), Finset.mem_univ j⟩
        · rintro ⟨hj, -⟩
          exact ⟨Finset.mem_univ j, fun hgij => hj (hg hgij).symm⟩
      rw [distinctCalls, hset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    rw [distinctCallPairs, Finset.sum_congr rfl (fun i _ => hcalls i), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have h := hcore g
  rw [hD] at h
  rw [hsub, hm] at h
  have hQ : (((m : ℚ) + 2) * ((m : ℚ) + 1))
        * ((∑ σ : Equiv.Perm α, (hits g σ) ^ 2 : ℕ) : ℚ)
      = ((((m : ℚ) + 2) * ((m : ℚ) + 1)) + (((m : ℚ) + 2) * ((m : ℚ) + 1)))
        * ((Fintype.card (Equiv.Perm α) : ℕ) : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h
  have hMne : ((m : ℚ) + 2) * ((m : ℚ) + 1) ≠ 0 := by positivity
  have hS2 : ((∑ σ : Equiv.Perm α, (hits g σ) ^ 2 : ℕ) : ℚ)
      = 2 * ((Fintype.card (Equiv.Perm α) : ℕ) : ℚ) := by
    refine mul_left_cancel₀ hMne ?_
    rw [hQ]
    ring
  simp only [Var, E]
  rw [hcastsum g, hcastsq g, hS2]
  field_simp
  norm_num
