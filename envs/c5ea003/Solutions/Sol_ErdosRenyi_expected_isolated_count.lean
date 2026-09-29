-- Prove2me | solution 1 for ErdosRenyi.expected_isolated_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:30:18.505811+00:00
-- url     : https://prove2.me/submissions/83346c54-9609-4fc1-a3cc-15fc61745476

import Mathlib
import Definitions.Def_Probability_NumberTheory_ErdosRenyiThreshold

open Finset ErdosRenyi in
theorem solution {n : ℕ} (p : ℝ) :
    Expect p (fun s : Finset (Edge n) => (isolatedCount s : ℝ))
      = n * (1 - p) ^ (n - 1) := by
  classical
  -- the probability that no edge of `T` is present
  have hprob : ∀ T : Finset (Edge n),
      ∑ s : Finset (Edge n), mass p s * (if Disjoint s T then (1 : ℝ) else 0)
        = (1 - p) ^ T.card := by
    intro T
    have hstep : ∀ s : Finset (Edge n),
        mass p s * (if Disjoint s T then (1 : ℝ) else 0)
          = if Disjoint s T then mass p s else 0 := by
      intro s
      by_cases h : Disjoint s T <;> simp [h]
    have hsetEq : (Finset.univ.filter (fun s : Finset (Edge n) => Disjoint s T))
        = Tᶜ.powerset := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
      constructor
      · intro h a ha
        exact Finset.mem_compl.2 (fun haT => (Finset.disjoint_left.1 h ha) haT)
      · intro h
        exact Finset.disjoint_left.2 (fun a ha haT => (Finset.mem_compl.1 (h ha)) haT)
    have hfilter : ∑ s : Finset (Edge n), mass p s * (if Disjoint s T then (1 : ℝ) else 0)
        = ∑ s ∈ Tᶜ.powerset, mass p s := by
      rw [Finset.sum_congr rfl (fun s _ => hstep s), ← Finset.sum_filter, hsetEq]
    rw [hfilter]
    have hTle : T.card ≤ Fintype.card (Edge n) := by
      simpa using Finset.card_le_univ T
    have hcompl : Tᶜ.card = Fintype.card (Edge n) - T.card := by
      rw [Finset.card_compl]
    have hsplit : ∀ s ∈ Tᶜ.powerset,
        mass p s = (1 - p) ^ T.card * (p ^ s.card * (1 - p) ^ (Tᶜ.card - s.card)) := by
      intro s hs
      have hsub : s ⊆ Tᶜ := Finset.mem_powerset.1 hs
      have hle : s.card ≤ Tᶜ.card := Finset.card_le_card hsub
      simp only [mass]
      rw [← mul_assoc, mul_comm ((1 - p) ^ T.card) (p ^ s.card), mul_assoc, ← pow_add]
      congr 2
      omega
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hone : ∑ s ∈ Tᶜ.powerset, p ^ s.card * (1 - p) ^ (Tᶜ.card - s.card) = 1 := by
      have hprodadd := Finset.prod_add (fun _ : Edge n => p) (fun _ : Edge n => 1 - p) Tᶜ
      simp only [Finset.prod_const] at hprodadd
      rw [show p + (1 - p) = 1 by ring, one_pow] at hprodadd
      have hsum : ∑ s ∈ Tᶜ.powerset, p ^ s.card * (1 - p) ^ (Tᶜ.card - s.card)
          = ∑ s ∈ Tᶜ.powerset, p ^ s.card * (1 - p) ^ (Tᶜ \ s).card := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hsub : s ⊆ Tᶜ := Finset.mem_powerset.1 hs
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
      rw [hsum, ← hprodadd]
    rw [hone, mul_one]
  -- membership in the incidence set
  have hmemv : ∀ (v : Fin n) (e : Edge n), e ∈ incident v ↔ v ∈ (e : Sym2 (Fin n)) := by
    intro v e
    simp [incident]
  -- each vertex is incident to `n - 1` potential edges
  have hinc : ∀ v : Fin n, (incident v).card = n - 1 := by
    intro v
    have hbij : (incident v).card = (Finset.univ.erase v).card := by
      refine Finset.card_bij'
        (fun e he => Sym2.Mem.other' ((hmemv v e).1 he))
        (fun u hu => (⟨s(v, u), by
            have hne : u ≠ v := (Finset.mem_erase.1 hu).1
            simp only [Sym2.mk_isDiag_iff]
            exact fun h => hne h.symm⟩ : Edge n))
        ?_ ?_ ?_ ?_
      · intro e he
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
        intro hcon
        have hv : v ∈ (e : Sym2 (Fin n)) := (hmemv v e).1 he
        have hcon' : Sym2.Mem.other' hv = v := hcon
        have hspec := Sym2.other_spec' hv
        apply e.2
        rw [← hspec, hcon']
        simp
      · intro u hu
        rw [hmemv]
        simp
      · intro e he
        have hv : v ∈ (e : Sym2 (Fin n)) := (hmemv v e).1 he
        have hspec := Sym2.other_spec' hv
        exact Subtype.ext hspec
      · intro u hu
        have hv : v ∈ (s(v, u) : Sym2 (Fin n)) := by simp
        have hspec := Sym2.other_spec' hv
        have := Sym2.congr_right.1 hspec
        exact this
    rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  -- linearity of expectation
  have hcount : ∀ s : Finset (Edge n), (isolatedCount s : ℝ)
      = ∑ v : Fin n, (if Disjoint s (incident v) then (1 : ℝ) else 0) := by
    intro s
    rw [isolatedCount, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases h : Disjoint s (incident v) <;> simp [h]
  calc Expect p (fun s : Finset (Edge n) => (isolatedCount s : ℝ))
      = ∑ s : Finset (Edge n), mass p s *
          ∑ v : Fin n, (if Disjoint s (incident v) then (1 : ℝ) else 0) := by
        rw [Expect]
        exact Finset.sum_congr rfl (fun s _ => by rw [hcount s])
    _ = ∑ v : Fin n, ∑ s : Finset (Edge n),
          mass p s * (if Disjoint s (incident v) then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [Finset.mul_sum]
    _ = ∑ _v : Fin n, (1 - p) ^ (n - 1) := by
        refine Finset.sum_congr rfl ?_
        intro v _
        rw [hprob (incident v), hinc v]
    _ = n * (1 - p) ^ (n - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
