-- Prove2me | solution 1 for BookSixth.hypergraph_two_color
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T23:59:44.080263+00:00
-- url     : https://prove2.me/submissions/1227fe2b-9025-4af7-baf0-c355273c833f

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

variable {N : ℕ}

/-- The colourings that are constantly `b` on `S`. -/
def monoOn (S : Finset (Fin N)) (b : Bool) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun c : Fin N → Bool => ∀ u ∈ S, c u = b)

theorem card_monoOn (S : Finset (Fin N)) (b : Bool) :
    (monoOn S b).card = 2 ^ (N - S.card) := by
  have hset : monoOn S b
      = Fintype.piFinset (fun u : Fin N => if u ∈ S then ({b} : Finset Bool) else Finset.univ) := by
    ext c
    simp only [monoOn, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h u
      by_cases hu : u ∈ S
      · simp [hu, h u hu]
      · simp [hu]
    · intro h u hu
      have := h u
      simpa [hu] using this
  rw [hset, Fintype.card_piFinset]
  have hprod : ∀ u : Fin N,
      (if u ∈ S then ({b} : Finset Bool) else Finset.univ).card = if u ∈ S then 1 else 2 := by
    intro u; by_cases hu : u ∈ S <;> simp [hu]
  rw [Finset.prod_congr rfl (fun u _ => hprod u)]
  have hfil : (Finset.univ.filter (fun u : Fin N => ¬ (u ∈ S))) = Sᶜ := by ext u; simp
  calc (∏ u : Fin N, if u ∈ S then 1 else 2)
      = 2 ^ (Finset.univ.filter (fun u : Fin N => ¬ (u ∈ S))).card := by
        rw [Finset.prod_ite]; simp
    _ = 2 ^ (N - S.card) := by rw [hfil, Finset.card_compl]; simp



/-- The colourings that are monochromatic on `S`. -/
def badOn (S : Finset (Fin N)) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun c : Fin N → Bool => ∀ u ∈ S, ∀ v ∈ S, c u = c v)

theorem badOn_eq (S : Finset (Fin N)) (hS : S.Nonempty) :
    badOn S = monoOn S false ∪ monoOn S true := by
  ext c
  simp only [badOn, monoOn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  obtain ⟨s, hs⟩ := hS
  constructor
  · intro h
    cases hcs : c s with
    | false => exact Or.inl (fun u hu => by rw [h u hu s hs, hcs])
    | true => exact Or.inr (fun u hu => by rw [h u hu s hs, hcs])
  · rintro (h | h) u hu v hv <;> rw [h u hu, h v hv]

theorem card_badOn (S : Finset (Fin N)) (hS : S.Nonempty) :
    (badOn S).card = 2 * 2 ^ (N - S.card) := by
  obtain ⟨s, hs⟩ := hS
  have hdisj : Disjoint (monoOn S false) (monoOn S true) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [monoOn, Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    have := (hc s hs).symm.trans (hc' s hs)
    exact absurd this (by simp)
  rw [badOn_eq S ⟨s, hs⟩, Finset.card_union_of_disjoint hdisj, card_monoOn, card_monoOn]
  ring

/-- The two constant colourings. -/
def consts : Finset (Fin N → Bool) := {(fun _ => false), (fun _ => true)}

theorem card_consts (hN : 1 ≤ N) : (consts (N := N)).card = 2 := by
  have hne : (fun _ => false : Fin N → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  rw [consts, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

theorem consts_subset (S : Finset (Fin N)) : consts ⊆ badOn S := by
  intro c hc
  simp only [consts, Finset.mem_insert, Finset.mem_singleton] at hc
  simp only [badOn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hc with rfl | rfl <;> intro u hu v hv <;> rfl



/-- Chapter 45, Theorem 1 (Erdős): a `d`-uniform family of at most `2^(d-1)` sets is
two-colourable. -/
theorem hypergraph_two_color {N d : ℕ} (hd : 2 ≤ d) (A : Finset (Finset (Fin N)))
    (hsize : ∀ S ∈ A, S.card = d) (hcard : A.card ≤ 2 ^ (d - 1)) :
    ∃ c : Fin N → Bool, ∀ S ∈ A, ∃ u ∈ S, ∃ v ∈ S, c u ≠ c v := by
  rcases Finset.eq_empty_or_nonempty A with rfl | ⟨S0, hS0⟩
  · exact ⟨fun _ => false, by simp⟩
  have hdN : d ≤ N := by
    have h1 : S0.card ≤ Fintype.card (Fin N) := Finset.card_le_univ S0
    rw [hsize S0 hS0] at h1
    simpa using h1
  have hN : 1 ≤ N := by omega
  -- every set of the family is nonempty and misses the two constant colourings only
  have hbadcard : ∀ S ∈ A, (badOn S \ consts).card = 2 * 2 ^ (N - d) - 2 := by
    intro S hS
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hsize S hS]; omega
    rw [Finset.card_sdiff_of_subset (consts_subset S), card_badOn S hne, hsize S hS, card_consts hN]
  -- the bad colourings
  have hsub : A.biUnion badOn ⊆ consts ∪ A.biUnion (fun S => badOn S \ consts) := by
    intro c hc
    rcases Finset.mem_biUnion.1 hc with ⟨S, hS, hcS⟩
    by_cases hcc : c ∈ consts
    · exact Finset.mem_union_left _ hcc
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨S, hS, Finset.mem_sdiff.2 ⟨hcS, hcc⟩⟩)
  have hK : 2 ≤ 2 * 2 ^ (N - d) := by
    have : 1 ≤ 2 ^ (N - d) := Nat.one_le_two_pow
    omega
  have hprod : 2 ^ (d - 1) * (2 * 2 ^ (N - d) - 2) = 2 ^ N - 2 ^ d := by
    have h1 : 2 ^ (d - 1) * 2 = 2 ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    have h2 : 2 ^ d * 2 ^ (N - d) = 2 ^ N := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 ^ (d - 1) * (2 * 2 ^ (N - d) - 2)
        = 2 ^ (d - 1) * 2 * 2 ^ (N - d) - 2 ^ (d - 1) * 2 := by
          rw [Nat.mul_sub, mul_assoc]
      _ = 2 ^ N - 2 ^ d := by rw [h1, h2]
  have hdle : 2 ^ d ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hdN
  have hd4 : 4 ≤ 2 ^ d := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hcardU : (A.biUnion badOn).card < 2 ^ N := by
    have e1 : (A.biUnion badOn).card ≤ (consts ∪ A.biUnion (fun S => badOn S \ consts)).card :=
      Finset.card_le_card hsub
    have e2 : (consts ∪ A.biUnion (fun S => badOn S \ consts)).card
        ≤ (consts (N := N)).card + (A.biUnion (fun S => badOn S \ consts)).card :=
      Finset.card_union_le _ _
    have e3 : (A.biUnion (fun S => badOn S \ consts)).card
        ≤ ∑ S ∈ A, (badOn S \ consts).card := Finset.card_biUnion_le
    have e4 : ∑ S ∈ A, (badOn S \ consts).card = A.card * (2 * 2 ^ (N - d) - 2) := by
      rw [Finset.sum_congr rfl hbadcard, Finset.sum_const, smul_eq_mul]
    have e5 : A.card * (2 * 2 ^ (N - d) - 2) ≤ 2 ^ N - 2 ^ d := by
      calc A.card * (2 * 2 ^ (N - d) - 2) ≤ 2 ^ (d - 1) * (2 * 2 ^ (N - d) - 2) :=
            Nat.mul_le_mul_right _ hcard
        _ = 2 ^ N - 2 ^ d := hprod
    rw [card_consts hN] at e2
    omega
  have hexists : ∃ c : Fin N → Bool, c ∉ A.biUnion badOn := by
    by_contra hcon
    push Not at hcon
    have hle : (Finset.univ : Finset (Fin N → Bool)).card ≤ (A.biUnion badOn).card :=
      Finset.card_le_card (fun c _ => hcon c)
    have : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by
      simp [Finset.card_univ]
    omega
  obtain ⟨c, hc⟩ := hexists
  refine ⟨c, fun S hS => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hc (Finset.mem_biUnion.2 ⟨S, hS, by
    simp only [badOn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcon⟩)

end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution {N d : ℕ} (hd : 2 ≤ d) (A : Finset (Finset (Fin N)))
    (hsize : ∀ S ∈ A, S.card = d) (hcard : A.card ≤ 2^(d-1)) :
    ∃ c : Fin N → Bool, ∀ S ∈ A, ∃ u ∈ S, ∃ v ∈ S, c u ≠ c v :=
  BookFix.hypergraph_two_color hd A hsize hcard
