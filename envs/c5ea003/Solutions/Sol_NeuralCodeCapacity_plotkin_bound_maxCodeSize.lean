-- Prove2me | solution 1 for NeuralCodeCapacity.plotkin_bound_maxCodeSize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:04:57.735438+00:00
-- url     : https://prove2.me/submissions/2e92286c-89be-437b-8f38-54ae7a8c7040

import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds

open NeuralCodeCapacity Finset in
theorem solution {N d : ℕ} (hNd : N < 2 * d) :
    maxCodeSize N d * (2 * d - N) ≤ 2 * d := by
  classical
  -- Plotkin's double count for a single separated code
  have key : ∀ C : Finset (NeuralCode N), Separated d C → C.card * (2 * d - N) ≤ 2 * d := by
    intro C hC
    set M := C.card with hM
    -- coordinatewise count of disagreeing ordered pairs
    have hcoord : ∀ i : Fin N, (∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ))
        = 2 * (C.filter (fun x => x i = true)).card * (C.filter (fun x => ¬ x i = true)).card := by
      intro i
      rw [← Finset.sum_filter_add_sum_filter_not C (fun x => x i = true)]
      have h1 : ∀ x ∈ C.filter (fun x => x i = true),
          (∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ)) = (C.filter (fun y => ¬ y i = true)).card := by
        intro x hx
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hxi := (Finset.mem_filter.1 hx).2
        cases hy : y i <;> simp [hxi, hy]
      have h2 : ∀ x ∈ C.filter (fun x => ¬ x i = true),
          (∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ)) = (C.filter (fun y => y i = true)).card := by
        intro x hx
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hxi : x i = false := by simpa using (Finset.mem_filter.1 hx).2
        cases hy : y i <;> simp [hxi, hy]
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul]
      ring
    have hS : ∑ x ∈ C, ∑ y ∈ C, hammingDist x y
        = ∑ i : Fin N, ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ) := by
      have hd : ∀ x y : NeuralCode N,
          hammingDist x y = ∑ i : Fin N, (if x i ≠ y i then 1 else 0 : ℕ) := fun x y => by
        rw [hammingDist, Finset.card_filter]
      rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hd x y]
      calc ∑ x ∈ C, ∑ y ∈ C, ∑ i : Fin N, (if x i ≠ y i then 1 else 0 : ℕ)
          = ∑ x ∈ C, ∑ i : Fin N, ∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ i : Fin N, ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ) := Finset.sum_comm
    -- upper bound: each coordinate contributes at most `M²/2`
    have hup : 2 * ∑ x ∈ C, ∑ y ∈ C, hammingDist x y ≤ N * (M * M) := by
      rw [hS, Finset.mul_sum]
      calc ∑ i : Fin N, 2 * ∑ x ∈ C, ∑ y ∈ C, (if x i ≠ y i then 1 else 0 : ℕ)
          ≤ ∑ _i : Fin N, M * M := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hcoord i]
            have hab : (C.filter (fun x => x i = true)).card
                + (C.filter (fun x => ¬ x i = true)).card = M :=
              Finset.card_filter_add_card_filter_not (s := C) (fun x => x i = true)
            set a := (C.filter (fun x => x i = true)).card
            set b := (C.filter (fun x => ¬ x i = true)).card
            rw [← hab]
            nlinarith [sq_nonneg ((a : ℤ) - b)]
        _ = N * (M * M) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    -- lower bound: distinct codewords are `d` apart
    have hlow : M * ((M - 1) * d) ≤ ∑ x ∈ C, ∑ y ∈ C, hammingDist x y := by
      calc M * ((M - 1) * d) = ∑ _x ∈ C, (M - 1) * d := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ C, ∑ y ∈ C, hammingDist x y := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [← Finset.add_sum_erase C _ hx]
          calc (M - 1) * d = ∑ _y ∈ C.erase x, d := by
                rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
            _ ≤ ∑ y ∈ C.erase x, hammingDist x y := Finset.sum_le_sum fun y hy =>
                hC x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
            _ ≤ hammingDist x x + ∑ y ∈ C.erase x, hammingDist x y := Nat.le_add_left _ _
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0, zero_mul]
      exact Nat.zero_le _
    have h2 : 2 * ((M - 1) * d) ≤ N * M := by
      have h3 : M * (2 * ((M - 1) * d)) ≤ M * (N * M) := by nlinarith [hup, hlow]
      exact Nat.le_of_mul_le_mul_left h3 hpos
    have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hpos
    zify [hNd.le, (show 1 ≤ M from hpos)] at h2 ⊢
    nlinarith [h2]
  -- the maximum is attained by some separated code
  obtain ⟨C, hCmem, hCeq⟩ := Finset.exists_mem_eq_sup
    ((Finset.univ : Finset (Finset (NeuralCode N))).filter (fun C => Separated d C))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩
    Finset.card
  unfold maxCodeSize
  rw [hCeq]
  exact key C (Finset.mem_filter.1 hCmem).2
