-- Prove2me | solution 2 for QuartetCodes.exists_quartet_avoiding_family
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:40:37.793499+00:00
-- url     : https://prove2.me/submissions/1d085469-dd09-463c-969b-ae4bcd35b656

import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes

open QuartetCodes Finset in
theorem solution (n m : ℕ) (h : n ^ 4 < 3 ^ m) :
    ∃ T : Fin (m + 1) → Equiv.Perm (Fin n), ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ i j, qcode (T i) a b c d ≠ qcode (T j) a b c d := by
  -- fewer than four leaves: nothing to separate
  by_cases hn : n < 4
  · refine ⟨fun _ => 1, fun a b c d hab hac had hbc hbd hcd => ?_⟩
    exfalso
    have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
    have := Fin.val_ne_of_ne hab; have := Fin.val_ne_of_ne hac; have := Fin.val_ne_of_ne had
    have := Fin.val_ne_of_ne hbc; have := Fin.val_ne_of_ne hbd; have := Fin.val_ne_of_ne hcd
    omega
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
  -- for distinct leaves the three quartet classes have equal size
  have hclass : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (qclass a b c d 1).card = (qclass a b c d 0).card ∧
        (qclass a b c d 2).card = (qclass a b c d 0).card := by
    intro a b c d hab hac had hbc hbd hcd
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
    exact ⟨hcard b c ![1, 0, 2] (by decide) hp1 0, hcard b d ![2, 1, 0] (by decide) hp2 0⟩
  have hmem' : ∀ (a b c d : Fin n) (π : Equiv.Perm (Fin n)) (t : Fin 3),
      π ∈ qclass a b c d t ↔ qcode π a b c d = t := by
    intro a b c d π t
    simp [qclass]
  -- each class is a third of all leaf orders
  have hthird : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      3 * (qclass a b c d 0).card = n.factorial := by
    intro a b c d hab hac had hbc hbd hcd
    obtain ⟨e1, e2⟩ := hclass a b c d hab hac had hbc hbd hcd
    have hfib := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm (Fin n))))
      (t := (univ : Finset (Fin 3))) (f := fun π => qcode π a b c d) (fun _ _ => mem_univ _)
    rw [Fin.sum_univ_three, card_univ, Fintype.card_perm, Fintype.card_fin] at hfib
    have q0 : (univ.filter fun π : Equiv.Perm (Fin n) => qcode π a b c d = 0) = qclass a b c d 0 := by
      ext π; rw [hmem']; simp
    have q1 : (univ.filter fun π : Equiv.Perm (Fin n) => qcode π a b c d = 1) = qclass a b c d 1 := by
      ext π; rw [hmem']; simp
    have q2 : (univ.filter fun π : Equiv.Perm (Fin n) => qcode π a b c d = 2) = qclass a b c d 2 := by
      ext π; rw [hmem']; simp
    rw [q0, q1, q2, e1, e2] at hfib
    omega
  -- the bad families: some quadruple sees a single quartet type throughout
  set N := n.factorial / 3 with hN
  have h3 : 3 * N = n.factorial := by
    rw [hN]
    exact Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))
  have hNpos : 0 < N := by
    have := Nat.factorial_pos n
    omega
  set Bad := (univ : Finset (Fin (m + 1) → Equiv.Perm (Fin n))).filter
    (fun T => ∃ q ∈ distinctQuads n,
      ∀ i, qcode (T i) q.1 q.2.1 q.2.2.1 q.2.2.2 = qcode (T 0) q.1 q.2.1 q.2.2.1 q.2.2.2)
    with hBad
  have hsub : Bad ⊆ (distinctQuads n).biUnion
      (fun q => sameCodeSet (0 : Fin (m + 1)) q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    intro T hT
    rw [hBad, mem_filter] at hT
    obtain ⟨-, q, hq, hall⟩ := hT
    rw [mem_biUnion]
    refine ⟨q, hq, ?_⟩
    simp only [sameCodeSet, mem_filter, mem_univ, true_and]
    exact hall
  have hsame : ∀ (a b c d : Fin n), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (sameCodeSet (0 : Fin (m + 1)) a b c d).card = 3 * N ^ (m + 1) := by
    intro a b c d hab hac had hbc hbd hcd
    obtain ⟨e1, e2⟩ := hclass a b c d hab hac had hbc hbd hcd
    have e0 : (qclass a b c d 0).card = N := by
      have := hthird a b c d hab hac had hbc hbd hcd
      omega
    have hsplit : sameCodeSet (0 : Fin (m + 1)) a b c d = (univ : Finset (Fin 3)).biUnion
        (fun t => Fintype.piFinset (fun _ : Fin (m + 1) => qclass a b c d t)) := by
      ext T
      simp only [sameCodeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Fintype.mem_piFinset, hmem']
      constructor
      · intro hh
        exact ⟨qcode (T 0) a b c d, fun i => hh i⟩
      · rintro ⟨t, ht⟩ i
        rw [ht i, ht 0]
    have hdisj : ∀ t ∈ (univ : Finset (Fin 3)), ∀ t' ∈ (univ : Finset (Fin 3)), t ≠ t' →
        Disjoint (Fintype.piFinset (fun _ : Fin (m + 1) => qclass a b c d t))
          (Fintype.piFinset (fun _ : Fin (m + 1) => qclass a b c d t')) := by
      intro t _ t' _ htt
      rw [Finset.disjoint_left]
      intro T g1 g2
      rw [Fintype.mem_piFinset] at g1 g2
      exact htt (((hmem' _ _ _ _ _ _).1 (g1 0)).symm.trans ((hmem' _ _ _ _ _ _).1 (g2 0)))
    rw [hsplit, Finset.card_biUnion hdisj]
    simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Fin.sum_univ_three, e1, e2, e0]
    ring
  have hdq : ∀ q ∈ distinctQuads n,
      (sameCodeSet (0 : Fin (m + 1)) q.1 q.2.1 q.2.2.1 q.2.2.2).card = 3 * N ^ (m + 1) := by
    intro q hq
    simp only [distinctQuads, mem_filter, mem_univ, true_and] at hq
    obtain ⟨h1, h2, h3', h4, h5, h6⟩ := hq
    exact hsame _ _ _ _ h1 h2 h3' h4 h5 h6
  have hcardQ : (distinctQuads n).card ≤ n ^ 4 := by
    calc (distinctQuads n).card ≤ (univ : Finset (Fin n × Fin n × Fin n × Fin n)).card :=
          card_le_card (subset_univ _)
      _ = n ^ 4 := by
          simp only [card_univ, Fintype.card_prod, Fintype.card_fin]
          ring
  have hBadlt : Bad.card < (univ : Finset (Fin (m + 1) → Equiv.Perm (Fin n))).card := by
    have hb1 : Bad.card ≤ (distinctQuads n).card * (3 * N ^ (m + 1)) := by
      calc Bad.card ≤ ((distinctQuads n).biUnion
            (fun q => sameCodeSet (0 : Fin (m + 1)) q.1 q.2.1 q.2.2.1 q.2.2.2)).card :=
            card_le_card hsub
        _ ≤ ∑ q ∈ distinctQuads n,
            (sameCodeSet (0 : Fin (m + 1)) q.1 q.2.1 q.2.2.1 q.2.2.2).card := card_biUnion_le
        _ = ∑ q ∈ distinctQuads n, 3 * N ^ (m + 1) := sum_congr rfl hdq
        _ = (distinctQuads n).card * (3 * N ^ (m + 1)) := by rw [sum_const, smul_eq_mul]
    have huniv : (univ : Finset (Fin (m + 1) → Equiv.Perm (Fin n))).card
        = 3 ^ (m + 1) * N ^ (m + 1) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin,
        ← h3, mul_pow]
    rw [huniv]
    have hNp : 0 < N ^ (m + 1) := pow_pos hNpos _
    calc Bad.card ≤ (distinctQuads n).card * (3 * N ^ (m + 1)) := hb1
      _ ≤ n ^ 4 * (3 * N ^ (m + 1)) := Nat.mul_le_mul_right _ hcardQ
      _ < 3 ^ m * (3 * N ^ (m + 1)) := Nat.mul_lt_mul_of_pos_right h (by omega)
      _ = 3 ^ (m + 1) * N ^ (m + 1) := by ring
  obtain ⟨T, -, hT⟩ := exists_mem_notMem_of_card_lt_card hBadlt
  refine ⟨T, fun a b c d hab hac had hbc hbd hcd => ?_⟩
  by_contra hcon
  apply hT
  rw [hBad, mem_filter]
  refine ⟨mem_univ _, (a, b, c, d), ?_, fun i => ?_⟩
  · simp only [distinctQuads, mem_filter, mem_univ, true_and]
    exact ⟨hab, hac, had, hbc, hbd, hcd⟩
  · by_contra hi
    exact hcon ⟨i, 0, hi⟩
