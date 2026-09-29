-- Prove2me | solution 1 for mme_dwz_finite_candidate_family_common_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:47:58.542922+00:00
-- url     : https://prove2.me/submissions/eaba6631-01ac-492f-b1bd-0b11acf55a3c

import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (candidates : Outer → Block → Finset Outer)
    (d : ℕ) (R : ℝ)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ D p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ D) ∧
      (D : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d D) < p ∧
      p ≤ 2 * max 4 (8 * max d D) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  classical
  let counts : Finset ℕ :=
    Finset.univ.image (fun x : Outer × Block ↦
      (candidates x.1 x.2).card)
  have hcounts : counts.Nonempty := by
    let x : Outer × Block := ⟨Classical.choice inferInstance,
      Classical.choice inferInstance⟩
    exact ⟨(candidates x.1 x.2).card,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  let D : ℕ := counts.max' hcounts
  have hDmem : D ∈ counts := by
    exact Finset.max'_mem counts hcounts
  have hD : ∀ retained small, (candidates retained small).card ≤ D := by
    intro retained small
    apply Finset.le_max' counts
    exact Finset.mem_image.mpr
      ⟨(retained, small), Finset.mem_univ (retained, small), rfl⟩
  have hDR : (D : ℝ) ≤ R := by
    obtain ⟨x, _hx, hxeq⟩ := Finset.mem_image.mp hDmem
    rw [← hxeq]
    exact hR x.1 x.2
  let Q : ℕ := max d D
  let M0 : ℕ := max 4 (8 * Q)
  have hM0 : 2 ≤ M0 := by
    exact le_trans (by decide) (le_max_left 4 (8 * Q))
  have hlevel : 4 ≤ M0 := le_max_left _ _
  have hfirst : 8 * d ≤ M0 := by
    exact le_trans (Nat.mul_le_mul_left 8 (le_max_left d D))
      (le_max_right 4 (8 * Q))
  have hcompatible : 8 * D ≤ M0 := by
    exact le_trans (Nat.mul_le_mul_left 8 (le_max_right d D))
      (le_max_right 4 (8 * Q))
  obtain ⟨p, hp, hpodd, h4p, hdp, hDp, hM0p, hpM0⟩ :=
    mme_dwz_claim6_8_exists_prime_modulus
      4 d D M0 hM0 hlevel hfirst hcompatible
  have hfamily : ∀ retained small,
      8 * (candidates retained small).card ≤ p := by
    intro retained small
    exact (Nat.mul_le_mul_left 8 (hD retained small)).trans hDp
  have hQR : (Q : ℝ) ≤ max (d : ℝ) R := by
    simp only [Q, Nat.cast_max]
    exact max_le_max (le_refl _) hDR
  have hpRate : (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
    by_cases hQ : Q = 0
    · have hp8 : p ≤ 8 := by
        dsimp only [M0] at hpM0
        simp only [hQ, Nat.mul_zero, max_eq_left (by decide : 0 ≤ 4)] at hpM0
        omega
      exact (show (p : ℝ) ≤ 8 by exact_mod_cast hp8).trans
        (le_max_left _ _)
    · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ
      have hp16 : p ≤ 16 * Q := by
        dsimp only [M0] at hpM0
        have h48 : 4 ≤ 8 * Q := by omega
        rw [max_eq_right h48] at hpM0
        omega
      have hp16R : (p : ℝ) ≤ 16 * (Q : ℝ) := by
        exact_mod_cast hp16
      calc
        (p : ℝ) ≤ 16 * (Q : ℝ) := hp16R
        _ ≤ 16 * max (d : ℝ) R := by gcongr
        _ ≤ max 8 (16 * max (d : ℝ) R) := le_max_right _ _
  refine ⟨D, p, hD, hDR, hp, hpodd, h4p, hdp, hfamily, ?_, ?_, hpRate⟩
  · simpa only [M0, Q] using hM0p
  · simpa only [M0, Q] using hpM0
