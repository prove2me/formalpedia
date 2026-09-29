-- Prove2me | solution 1 for mme_dwz_q5_actual_standard_products_of_numeric_budgets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T22:08:03.150427+00:00
-- url     : https://prove2.me/submissions/a3785636-3d14-42b2-805b-eb058df8904b

import Theorems.Thm_mme_dwz_q5_exact_global_counting_families
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_dwz_prime_hash_budget_to_actual_standard_products
import Mathlib.Tactic.FinCases

open BigOperators MME MME.TensorObj MME.StothersFourth MME.DWZSimultaneous
  MME.DWZRestrictedValue MME.CompleteSplit.CWFourth MME.CompleteSplit
  MME.DWZComponentRestriction MME.DWZStep1Support
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (t modulus r : ℕ) (ht : 0 < t)
    [Fact modulus.Prime]
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (hmodulus : 8 < modulus) :
    let D := ∏ c : Fin 45, (rawProfile c).denominator
    let m := fun c : Fin 45 ↦ component c * (D * t) / (rawProfile c).denominator
    let n := fun c : Fin 45 ↦ (rawProfile c).length (m c)
    let N := ∑ c : Fin 45, n c
    let shape : Fin 45 → Fin 3 → ℕ := fun c i ↦ (coarseAddress c i).val
    let z := fun c (l : Fin 5) ↦ (rawProfile c).count l * m c
    let mu : Fin 3 → Fin 45 → Fin 5 → ℕ := fun
      | 0, c, l => if shape c 1 = 0 then z c (Fin.rev l) else 0
      | 1, c, l => if shape c 0 = 0 then z c (Fin.rev l) else 0
      | 2, c, l => z c l
    let M : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin 45 // shape c i = g}, n c.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let tables : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g.val)
    let degree := fun mode : Fin 3 ↦
      ∑ h ∈ tables, ∏ g : Fin 9, (M mode g.val).factorial /
        ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial
    let coarse := fun c : Fin 45 ↦ coarseAddress c 2
    let boundary := fun c : Fin 45 ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F := fun i : Fin 9 × Fin 5 ↦
      ∑ c : {c : Fin 45 // coarse c = i.1}, mu 2 c.val i.2
    let pooled : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ := fun
      | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let collapse := fun c : Fin 45 ↦ if boundary c then Sum.inl c else Sum.inr (coarse c)
    let W :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (pooled di.val).factorial) *
      (∏ d : Fin 45 ⊕ Fin 9, (∑ i, pooled (d,i)).factorial /
        ∏ c : {c : Fin 45 // collapse c = d}, (n c.val).factorial)
    4 * max (degree 0) (degree 1) ≤ modulus →
    8 * (W - 1) ≤ modulus →
    8 * modulus ^ 2 * (r * (3 * N + 2)) ≤
      3 * (N.factorial / ∏ c, (n c).factorial) * S.card →
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
        (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (rawProfile c) (m c))))
      ((CWObj K 5).kronPow (N * 4)) := by
  classical
  intro D m n N shape z mu M Cell tables degree coarse boundary F pooled collapse W
    hxyBudget hzBudget hbudget
  obtain ⟨_hD, _hNformula, _hnformula, _hnpositive, _hmformula, hN,
    R, word, targets, _hword, howner, hmarginal, _hsupported,
    hcomplete, _hmem, _hwords, hcard, _hnonempty, hpositions,
    hdegrees, hcompatible, _huseful⟩ :=
      mme_dwz_q5_exact_global_counting_families t ht
  obtain ⟨positions, hcell⟩ := hpositions
  obtain ⟨_hscale, _hpositive, _htotal, _halpha, hgrade, _hinj,
    _hcounts, _hsums, _hxy, _hequiv, hsupport⟩ :=
      mme_dwz_q5_exact_global_profile_certificate
  have hsum : ∀ c, shape c 0 + shape c 1 + shape c 2 = 8 := by
    intro c
    simpa only [Fin.sum_univ_succ, Nat.add_assoc, Nat.add_zero] using hgrade c
  have hlength : N - 1 + 1 = N := Nat.sub_add_cancel hN
  let reindex : Fin (N - 1 + 1) ≃ Fin N := finCongr hlength
  apply mme_dwz_prime_hash_budget_to_actual_standard_products
    5 N (N - 1) modulus R 45 r (by decide) hN
    (fun c ↦ coarseAddress c 0) (fun c ↦ coarseAddress c 1)
    (fun c ↦ coarseAddress c 2) rawProfile m word shape
    (by intro c i; fin_cases i <;> rfl) hsum mu
    (by intro c a; rfl)
    (by
      intro c hc a
      change z c a = if shape c 0 = 0 then z c (Fin.rev (Fin.rev a)) else 0
      rw [if_pos hc, Fin.rev_rev])
    (by
      intro c hc a
      change z c a = if shape c 1 = 0 then z c (Fin.rev (Fin.rev a)) else 0
      rw [if_pos hc, Fin.rev_rev])
    M targets Finset.univ (Finset.subset_univ _) (fun a _ ↦ hmarginal a)
    (by intro a hs hm; obtain ⟨b,hb⟩ := hcomplete a hs hm
        exact ⟨b, Finset.mem_univ _, hb⟩)
    howner.injOn positions hcell hsupport reindex S hSrange hSfree
    hpodd hmodulus (max (degree 0) (degree 1)) (W - 1) hxyBudget hzBudget
  · intro a _
    rw [hdegrees 0 a]
    exact Nat.le_max_left _ _
  · intro a _
    rw [hdegrees 1 a]
    exact Nat.le_max_right _ _
  · intro a ha f hf
    exact ((hcompatible a ha f hf.1 hf.2).2.1).le
  · simpa only [hcard] using hbudget

