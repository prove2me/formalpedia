-- Prove2me | solution 1 for BookSixth.ramsey_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T01:07:11.381448+00:00
-- url     : https://prove2.me/submissions/ec607712-81a0-48a3-9008-ad9eb0cb34cf

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

/-- `2^(k+2) ≤ (k!)²` for `k ≥ 3`. -/
theorem pow_le_factorial_sq : ∀ k : ℕ, 3 ≤ k → 2 ^ (k + 2) ≤ (Nat.factorial k) ^ 2 := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · omega
      · omega
      · norm_num [Nat.factorial]
    · have hprev := ih (by omega)
      have hfac : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := rfl
      calc 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
        _ ≤ 2 * (Nat.factorial m) ^ 2 := by omega
        _ ≤ (m + 1) ^ 2 * (Nat.factorial m) ^ 2 := by
            refine Nat.mul_le_mul_right _ ?_
            nlinarith
        _ = (Nat.factorial (m + 1)) ^ 2 := by rw [hfac]; ring

/-- The Erdős counting inequality, in natural numbers. -/
theorem ramsey_arith {k N : ℕ} (hk : 3 ≤ k) (hN : N ^ 2 < 2 ^ k) :
    2 * Nat.choose N k < 2 ^ (Nat.choose k 2) := by
  have hdesc : Nat.factorial k * Nat.choose N k = Nat.descFactorial N k :=
    (Nat.descFactorial_eq_factorial_mul_choose N k).symm
  have hle : Nat.factorial k * Nat.choose N k ≤ N ^ k := by
    rw [hdesc]; exact Nat.descFactorial_le_pow N k
  have hchoose2 : Nat.choose k 2 * 2 = k * (k - 1) := by
    rw [Nat.choose_two_right]
    have hdvd : 2 ∣ k * (k - 1) := by
      cases k with
      | zero => simp
      | succ j =>
        simpa [Nat.succ_sub_one, Nat.mul_comm] using (Nat.even_mul_succ_self j).two_dvd
    omega
  -- square everything
  have hsq1 : (Nat.factorial k) ^ 2 * (Nat.choose N k) ^ 2 ≤ (N ^ 2) ^ k := by
    calc (Nat.factorial k) ^ 2 * (Nat.choose N k) ^ 2
        = (Nat.factorial k * Nat.choose N k) ^ 2 := by ring
      _ ≤ (N ^ k) ^ 2 := Nat.pow_le_pow_left hle 2
      _ = (N ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hsq2 : (N ^ 2) ^ k < (2 ^ k) ^ k := by
    refine Nat.pow_lt_pow_left hN (by omega)
  have hkey : 4 * (Nat.choose N k) ^ 2 * (Nat.factorial k) ^ 2 < 2 ^ (k * k) * 4 := by
    have h1 : (Nat.factorial k) ^ 2 * (Nat.choose N k) ^ 2 < 2 ^ (k * k) := by
      calc (Nat.factorial k) ^ 2 * (Nat.choose N k) ^ 2 ≤ (N ^ 2) ^ k := hsq1
        _ < (2 ^ k) ^ k := hsq2
        _ = 2 ^ (k * k) := by rw [← pow_mul]
    nlinarith [h1]
  have hfk := pow_le_factorial_sq k hk
  have hexp : k * k + 2 = k * (k - 1) + (k + 2) := by
    cases k with
    | zero => omega
    | succ j => simp only [Nat.succ_sub_one]; ring
  have hsplit : 2 ^ (k * k) * 4 = 2 ^ (k * (k - 1)) * 2 ^ (k + 2) := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add, ← pow_add, hexp]
  have hfinal : (2 * Nat.choose N k) ^ 2 < (2 ^ (Nat.choose k 2)) ^ 2 := by
    have hR : (2 ^ (Nat.choose k 2)) ^ 2 = 2 ^ (k * (k - 1)) := by
      rw [← pow_mul, hchoose2]
    rw [hR]
    have hL : (2 * Nat.choose N k) ^ 2 = 4 * (Nat.choose N k) ^ 2 := by ring
    rw [hL]
    have hfacpos : 0 < (Nat.factorial k) ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    have : 2 ^ (k * (k - 1)) * (Nat.factorial k) ^ 2 ≤ 4 * (Nat.choose N k) ^ 2 * (Nat.factorial k) ^ 2 :=
      Nat.mul_le_mul_right _ hcon
    have h2 : 2 ^ (k * (k - 1)) * 2 ^ (k + 2) ≤ 2 ^ (k * (k - 1)) * (Nat.factorial k) ^ 2 :=
      Nat.mul_le_mul_left _ hfk
    omega
  by_contra hcon
  push Not at hcon
  exact absurd (Nat.pow_le_pow_left hcon 2) (by omega)


/-- Counting the colourings of a finite index type prescribed on a subset. -/
theorem card_prescribed {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) (b : Bool) :
    (Finset.univ.filter (fun c : ι → Bool => ∀ u ∈ T, c u = b)).card
      = 2 ^ (Fintype.card ι - T.card) := by
  classical
  have hset : (Finset.univ.filter (fun c : ι → Bool => ∀ u ∈ T, c u = b))
      = Fintype.piFinset (fun u : ι => if u ∈ T then ({b} : Finset Bool) else Finset.univ) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h u
      by_cases hu : u ∈ T
      · simp [hu, h u hu]
      · simp [hu]
    · intro h u hu
      have := h u
      simpa [hu] using this
  rw [hset, Fintype.card_piFinset]
  have hprod : ∀ u : ι,
      (if u ∈ T then ({b} : Finset Bool) else Finset.univ).card = if u ∈ T then 1 else 2 := by
    intro u; by_cases hu : u ∈ T <;> simp [hu]
  rw [Finset.prod_congr rfl (fun u _ => hprod u)]
  have hfil : (Finset.univ.filter (fun u : ι => ¬ (u ∈ T))) = Tᶜ := by ext u; simp
  calc (∏ u : ι, if u ∈ T then 1 else 2)
      = 2 ^ (Finset.univ.filter (fun u : ι => ¬ (u ∈ T))).card := by
        rw [Finset.prod_ite]; simp
    _ = 2 ^ (Fintype.card ι - T.card) := by rw [hfil, Finset.card_compl]

/-- The ordered pairs from `S` in increasing order. -/
def upairs {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (S ×ˢ S).filter (fun p => p.1 < p.2)

theorem card_upairs {N : ℕ} (S : Finset (Fin N)) : (upairs S).card = Nat.choose S.card 2 := by
  classical
  set T := upairs S with hT
  set T' := (S ×ˢ S).filter (fun p : Fin N × Fin N => p.2 < p.1) with hT'
  have hswap : T'.card = T.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [hT', hT, upairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p hp q hq h
      simpa [Prod.ext_iff, and_comm] using h
    · intro p hp
      simp only [hT, upairs, Finset.mem_filter, Finset.mem_product] at hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [hT', Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hunion : S.offDiag = T ∪ T' := by
    ext p
    simp only [Finset.mem_offDiag, hT, hT', upairs, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1, h2, ne_of_lt h3⟩
      · exact ⟨h1, h2, (ne_of_lt h3).symm⟩
  have hdisj : Disjoint T T' := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [hT, hT', upairs, Finset.mem_filter] at hp hp'
    exact absurd hp.2 (not_lt.2 (le_of_lt hp'.2))
  have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
  rw [hunion, Finset.card_union_of_disjoint hdisj, hswap] at hoff
  have hmul : S.card * (S.card - 1) = S.card * S.card - S.card := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [Nat.choose_two_right, hmul]
  omega


/-- The unordered key of a pair of distinct vertices. -/
def key {N : ℕ} (u v : Fin N) : Fin N × Fin N := if u ≤ v then (u, v) else (v, u)

theorem key_symm {N : ℕ} {u v : Fin N} : key u v = key v u := by
  unfold key
  rcases le_total u v with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp
    · rw [if_pos h, if_neg (by exact not_le.2 hlt)]
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp
    · rw [if_neg (by exact not_le.2 hlt), if_pos h]

theorem key_of_lt {N : ℕ} {u v : Fin N} (h : u < v) : key u v = (u, v) := by
  unfold key; rw [if_pos (le_of_lt h)]

/-- The graph determined by a colouring of vertex pairs. -/
def graphOf {N : ℕ} (c : Fin N × Fin N → Bool) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun u v => c (key u v) = true)

theorem adj_iff {N : ℕ} (c : Fin N × Fin N → Bool) {u v : Fin N} (h : u < v) :
    (graphOf c).Adj u v ↔ c (u, v) = true := by
  rw [graphOf, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h2 | h2⟩
    · rwa [key_of_lt h] at h2
    · rw [key_symm, key_of_lt h] at h2; exact h2
  · intro h2
    exact ⟨ne_of_lt h, Or.inl (by rwa [key_of_lt h])⟩

theorem ramsey_counting (k N : ℕ) (hk : 3 ≤ k) (hsq : N ^ 2 < 2 ^ k) (hNk : k ≤ N) :
    ∃ G : SimpleGraph (Fin N), NoMono k G := by
  classical
  have hcardι : Fintype.card (Fin N × Fin N) = N ^ 2 := by simp [pow_two]
  set bad : Finset (Fin N × Fin N → Bool) :=
    ((Finset.univ : Finset (Fin N)).powersetCard k).biUnion
      (fun S => (Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = true))
              ∪ (Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = false)))
    with hbad
  have hC2 : Nat.choose k 2 ≤ N ^ 2 := by
    have h1 : Nat.choose k 2 ≤ k * k := by
      rw [Nat.choose_two_right]
      have : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left _ (by omega)
      omega
    have h2 : k * k ≤ N * N := Nat.mul_le_mul hNk hNk
    calc Nat.choose k 2 ≤ k * k := h1
      _ ≤ N * N := h2
      _ = N ^ 2 := by ring
  have hpiece : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
      ((Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = true))
        ∪ (Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = false))).card
        ≤ 2 * 2 ^ (N ^ 2 - Nat.choose k 2) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hcu : (upairs S).card = Nat.choose k 2 := by rw [card_upairs, hS.2]
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [card_prescribed (upairs S) true, card_prescribed (upairs S) false, hcardι, hcu]
    omega
  have hcardbad : bad.card < 2 ^ (N ^ 2) := by
    have h1 : bad.card ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        (2 * 2 ^ (N ^ 2 - Nat.choose k 2)) := by
      refine le_trans Finset.card_biUnion_le ?_
      exact Finset.sum_le_sum hpiece
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    have harith := ramsey_arith hk hsq
    have hsplit : 2 ^ (N ^ 2) = 2 ^ (Nat.choose k 2) * 2 ^ (N ^ 2 - Nat.choose k 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hpos : 0 < 2 ^ (N ^ 2 - Nat.choose k 2) := Nat.two_pow_pos _
    have h2 : Nat.choose N k * (2 * 2 ^ (N ^ 2 - Nat.choose k 2))
        < 2 ^ (Nat.choose k 2) * 2 ^ (N ^ 2 - Nat.choose k 2) := by
      have := Nat.mul_lt_mul_of_lt_of_le harith (le_refl (2 ^ (N ^ 2 - Nat.choose k 2))) hpos
      calc Nat.choose N k * (2 * 2 ^ (N ^ 2 - Nat.choose k 2))
          = (2 * Nat.choose N k) * 2 ^ (N ^ 2 - Nat.choose k 2) := by ring
        _ < 2 ^ (Nat.choose k 2) * 2 ^ (N ^ 2 - Nat.choose k 2) := this
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin N × Fin N → Bool, c ∉ bad := by
    by_contra hcon
    push Not at hcon
    have hle : (Finset.univ : Finset (Fin N × Fin N → Bool)).card ≤ bad.card :=
      Finset.card_le_card fun c _ => hcon c
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, hcardι] at hle
    omega
  refine ⟨graphOf c, ?_⟩
  intro S hS
  have hSmem : S ∈ (Finset.univ : Finset (Fin N)).powersetCard k :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ S, hS⟩
  have hnot : c ∉ (Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = true))
      ∪ (Finset.univ.filter (fun c : Fin N × Fin N → Bool => ∀ p ∈ upairs S, c p = false)) := by
    intro hmem
    exact hc (Finset.mem_biUnion.2 ⟨S, hSmem, hmem⟩)
  rw [Finset.mem_union] at hnot
  push Not at hnot
  obtain ⟨hnt, hnf⟩ := hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnt hnf
  obtain ⟨p, hp, hpv⟩ := hnf
  obtain ⟨q, hq, hqv⟩ := hnt
  have hmemp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 := by
    simp only [upairs, Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hmemq : q.1 ∈ S ∧ q.2 ∈ S ∧ q.1 < q.2 := by
    simp only [upairs, Finset.mem_filter, Finset.mem_product] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  constructor
  · refine ⟨p.1, hmemp.1, p.2, hmemp.2.1, ne_of_lt hmemp.2.2, ?_⟩
    rw [adj_iff c hmemp.2.2]
    cases hcp : c p with
    | false => exact absurd hcp (by simpa using hpv)
    | true => rw [← hcp]
  · refine ⟨q.1, hmemq.1, q.2, hmemq.2.1, ne_of_lt hmemq.2.2, ?_⟩
    rw [adj_iff c hmemq.2.2]
    intro hcontra
    exact hqv (by rw [← hcontra])

theorem ramsey_real_bound (k N : ℕ) (hk : 2 ≤ k) (hN : (N : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin N), NoMono k G := by
  classical
  -- the square of the hypothesis is a statement about naturals
  have hsq : N ^ 2 < 2 ^ k := by
    have h0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hr : ((2:ℝ) ^ ((k:ℝ)/2)) ^ 2 = (2:ℝ) ^ (k : ℕ) := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ ((k:ℝ)/2)) 2, ← Real.rpow_mul (by norm_num)]
      rw [show (k:ℝ)/2 * (2:ℕ) = (k:ℝ) by push_cast; ring]
      rw [Real.rpow_natCast]
    have hlt : ((N:ℝ)) ^ 2 < ((2:ℝ) ^ ((k:ℝ)/2)) ^ 2 := by
      have hpos : (0:ℝ) < (2:ℝ) ^ ((k:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
      nlinarith [hN, h0, hpos]
    rw [hr] at hlt
    exact_mod_cast hlt
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · -- k = 2, so N ≤ 1 and there are no k-subsets
    have hk2 : k = 2 := by omega
    subst hk2
    refine ⟨⊥, ?_⟩
    intro S hS
    exfalso
    have h1 : S.card ≤ Fintype.card (Fin N) := Finset.card_le_univ S
    simp only [Fintype.card_fin] at h1
    have : N ^ 2 < 4 := by simpa using hsq
    nlinarith [h1, hS, this]
  · -- the counting argument
    rcases Nat.lt_or_ge N k with hNk | hNk
    · refine ⟨⊥, ?_⟩
      intro S hS
      exfalso
      have h1 : S.card ≤ Fintype.card (Fin N) := Finset.card_le_univ S
      simp only [Fintype.card_fin, hS] at h1
      omega
    · exact ramsey_counting k N hk3 hsq hNk

end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution (k N : ℕ) (hk : 2 ≤ k) (hN : (N : ℝ) < (2 : ℝ)^((k : ℝ)/2)) :
    ∃ G : SimpleGraph (Fin N), NoMono k G :=
  BookFix.ramsey_real_bound k N hk hN
