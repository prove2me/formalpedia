-- Prove2me | solution 2 for NeuralCodePlotkinTightness.hadamard_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:00:03.286808+00:00
-- url     : https://prove2.me/submissions/0fc6e968-b857-4e18-9048-756288c6f3f3

import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness

open NeuralCodePlotkinTightness Finset NeuralCodeCapacity in
theorem solution (m : ℕ) :
    maxCodeSize (2 ^ (m + 1)) (2 ^ m) = 2 ^ (m + 2) := by
  classical
  -- Plotkin's double count
  have plotkin : ∀ (N d : ℕ), N < 2 * d → ∀ C : Finset (NeuralCode N), Separated d C →
      C.card * (2 * d - N) ≤ 2 * d := by
    intro N d hNd C hC
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
  -- shortening: split by the first bit and delete that coordinate
  have hshort : ∀ (N d : ℕ), 0 < N → N - 1 < 2 * d → ∀ C : Finset (NeuralCode N),
      Separated d C → C.card * (2 * d - (N - 1)) ≤ 2 * (2 * d) := by
    intro N d hN hlt C hC
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hlt ⊢
    have hhalf : ∀ β : Bool, (C.filter (fun c => c 0 = β)).card * (2 * d - N') ≤ 2 * d := by
      intro β
      have h0 : ∀ c ∈ C.filter (fun c => c 0 = β), ∀ c' ∈ C.filter (fun c => c 0 = β),
          c 0 = c' 0 := by
        intro c hc c' hc'
        rw [(Finset.mem_filter.1 hc).2, (Finset.mem_filter.1 hc').2]
      have hinj : Set.InjOn (fun c : NeuralCode (N' + 1) => c ∘ Fin.succ)
          (C.filter (fun c => c 0 = β) : Set (NeuralCode (N' + 1))) := by
        intro c hc c' hc' h
        funext i
        exact Fin.cases (h0 c hc c' hc') (fun j => congrFun h j) i
      have hdist : ∀ c ∈ C.filter (fun c => c 0 = β), ∀ c' ∈ C.filter (fun c => c 0 = β),
          hammingDist (c ∘ Fin.succ) (c' ∘ Fin.succ) = hammingDist c c' := by
        intro c hc c' hc'
        have hcc := h0 c hc c' hc'
        simp only [hammingDist]
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
        simp only [hcc, Function.comp, ne_eq, not_true_eq_false, if_false, zero_add]
        exact Finset.sum_congr rfl fun x _ => by split_ifs <;> rfl
      have hsep : Separated d ((C.filter (fun c => c 0 = β)).image (fun c => c ∘ Fin.succ)) := by
        intro x hx y hy hxy
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hy
        rw [hdist c hc c' hc']
        exact hC c (Finset.mem_filter.1 hc).1 c' (Finset.mem_filter.1 hc').1
          (fun h => hxy (by rw [h]))
      have h := plotkin N' d hlt _ hsep
      rwa [Finset.card_image_of_injOn hinj] at h
    have hsplit := Finset.card_filter_add_card_filter_not (s := C) (fun c => c 0 = true)
    have hfalse : C.filter (fun c => ¬ c 0 = true) = C.filter (fun c => c 0 = false) := by
      ext c
      simp
    rw [hfalse] at hsplit
    have h1 := hhalf true
    have h2 := hhalf false
    rw [← hsplit, add_mul]
    omega
  -- half of all strings satisfy `⟨u, x⟩ = 1` when `u ≠ 0`
  have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hbitnot : ∀ β : Bool, bit (!β) = bit β + 1 := by decide
  have hflip : ∀ (u : Fin (m + 1) → Bool) (j : Fin (m + 1)), u j = true →
      ∀ x : Fin (m + 1) → Bool, ip u (Function.update x j (!x j)) = ip u x + 1 := by
    intro u j hj x
    unfold ip
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest : ∑ i ∈ univ.erase j, bit (u i) * bit (Function.update x j (!x j) i)
        = ∑ i ∈ univ.erase j, bit (u i) * bit (x i) :=
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest, Function.update_self, hj, hbitnot]
    simp only [bit, if_true]
    ring
  have hhalf2 : ∀ u : Fin (m + 1) → Bool, (∃ j, u j = true) →
      (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 1)).card = 2 ^ m ∧
      (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 0)).card = 2 ^ m := by
    rintro u ⟨j, hj⟩
    have hfl : ∀ x : Fin (m + 1) → Bool,
        Function.update (Function.update x j (!x j)) j (!(Function.update x j (!x j)) j) = x := by
      intro x
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [Function.update_of_ne hi]
    have heq : (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 1)).card
        = (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 0)).card := by
      exact Finset.card_bij' (fun x _ => Function.update x j (!x j))
        (fun x _ => Function.update x j (!x j))
        (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          rw [hflip u j hj, (Finset.mem_filter.1 hx).2]; decide⟩)
        (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          rw [hflip u j hj, (Finset.mem_filter.1 hx).2]; decide⟩)
        (fun x _ => hfl x) (fun x _ => hfl x)
    have htot : (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 1)).card
        + (univ.filter (fun x : Fin (m + 1) → Bool => ip u x = 0)).card = 2 ^ (m + 1) := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin (m + 1) → Bool))) (fun x => ip u x = 1)
      have hne : (univ.filter (fun x : Fin (m + 1) → Bool => ¬ ip u x = 1))
          = univ.filter (fun x => ip u x = 0) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases htwo (ip u x) with h' | h' <;> simp [h']
      rw [hne, Finset.card_univ] at h
      rw [h]
      simp
    rw [pow_succ] at htot
    omega
  -- distinct affine words differ in at least `2^m` places
  have hword : ∀ (a a' : Fin (m + 1) → Bool) (b b' : Bool), (a, b) ≠ (a', b') →
      2 ^ m ≤ (univ.filter (fun x => affineWord a b x ≠ affineWord a' b' x)).card := by
    intro a a' b b' hne
    have hbitx : ∀ p q : Bool, bit (xor p q) = bit p + bit q := by decide
    have hip : ∀ x, ip a x + ip a' x = ip (fun i => xor (a i) (a' i)) x := by
      intro x
      unfold ip
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbitx]
      ring
    have hdiff : ∀ x, affineWord a b x ≠ affineWord a' b' x ↔
        ip (fun i => xor (a i) (a' i)) x + bit b + bit b' = 1 := by
      intro x
      unfold affineWord
      rw [← hip x]
      rcases htwo (ip a x) with h1 | h1 <;> rcases htwo (ip a' x) with h2 | h2 <;>
        cases b <;> cases b' <;> simp only [h1, h2] <;> decide
    by_cases ha : a = a'
    · subst ha
      have hb : b ≠ b' := fun h => hne (by rw [h])
      have hall : univ.filter (fun x => affineWord a b x ≠ affineWord a b' x) = univ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rw [hdiff]
        have hu0 : ip (fun i => xor (a i) (a i)) x = 0 := by
          unfold ip
          refine Finset.sum_eq_zero fun i _ => ?_
          simp [bit]
        rw [hu0]
        cases b <;> cases b' <;> first | exact absurd rfl hb | decide
      rw [hall, Finset.card_univ]
      simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ : ∃ j, xor (a j) (a' j) = true := by
        by_contra hno
        apply ha
        funext i
        have hi : ¬ xor (a i) (a' i) = true := fun h => hno ⟨i, h⟩
        have key : ∀ p q : Bool, ¬ xor p q = true → p = q := by decide
        exact key _ _ hi
      obtain ⟨h1, h0⟩ := hhalf2 (fun i => xor (a i) (a' i)) ⟨j, hj⟩
      rcases htwo (bit b + bit b') with hc | hc
      · have hset : univ.filter (fun x => affineWord a b x ≠ affineWord a' b' x)
            = univ.filter (fun x => ip (fun i => xor (a i) (a' i)) x = 1) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hdiff, add_assoc, hc, add_zero]
        rw [hset, h1]
      · have hset : univ.filter (fun x => affineWord a b x ≠ affineWord a' b' x)
            = univ.filter (fun x => ip (fun i => xor (a i) (a' i)) x = 0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hdiff, add_assoc, hc]
          rcases htwo (ip (fun i => xor (a i) (a' i)) x) with h | h <;> rw [h] <;> decide
        rw [hset, h0]
  -- Hamming distance after relabelling the neurons by strings
  have hham : ∀ f g : (Fin (m + 1) → Bool) → Bool,
      hammingDist (f ∘ (strEquiv (m + 1)).symm : NeuralCode (2 ^ (m + 1)))
        (g ∘ (strEquiv (m + 1)).symm) = (univ.filter (fun x => f x ≠ g x)).card := by
    intro f g
    unfold hammingDist
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr ((strEquiv (m + 1)).symm.subtypeEquiv (fun i => Iff.rfl))
  have hsepA : Separated (2 ^ m) (affineCode (m + 1)) := by
    intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨⟨a', b'⟩, -, rfl⟩ := Finset.mem_image.1 hy
    rw [hham]
    refine hword a a' b b' fun h => hxy ?_
    rw [Prod.mk.injEq] at h
    rw [h.1, h.2]
  have hcardA : (affineCode (m + 1)).card = 2 ^ (m + 2) := by
    unfold affineCode
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ]
      simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      ring
    · intro p p' h
      by_contra hpp
      have hw := hword p.1 p'.1 p.2 p'.2 (by simpa using hpp)
      rw [← hham] at hw
      simp only at h
      rw [h, hammingDist_self] at hw
      have : 0 < 2 ^ m := by positivity
      omega
  apply le_antisymm
  · unfold maxCodeSize
    apply Finset.sup_le
    intro C hC
    have hCsep := (Finset.mem_filter.1 hC).2
    have hpos : 0 < 2 ^ (m + 1) := by positivity
    have hp1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hlt : 2 ^ (m + 1) - 1 < 2 * 2 ^ m := by rw [pow_succ]; omega
    have h := hshort (2 ^ (m + 1)) (2 ^ m) hpos hlt C hCsep
    have h2 : 2 * 2 ^ m - (2 ^ (m + 1) - 1) = 1 := by rw [pow_succ]; omega
    rw [h2, mul_one] at h
    calc C.card ≤ 2 * (2 * 2 ^ m) := h
      _ = 2 ^ (m + 2) := by ring
  · unfold maxCodeSize
    rw [← hcardA]
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hsepA⟩)
