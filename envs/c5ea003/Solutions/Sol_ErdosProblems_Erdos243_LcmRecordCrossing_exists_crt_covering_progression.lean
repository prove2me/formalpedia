-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.exists_crt_covering_progression
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:53:19.006674+00:00
-- url     : https://prove2.me/submissions/12776e27-3971-413f-8124-4f3e26409f80

import Mathlib
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_covering_of_crt_block
open ErdosProblems.Erdos243 ErdosProblems.Erdos243.LcmRecordCrossing

private theorem exists_consecutiveMultiples_between
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x, (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧ ∀ i : Fin k, m i ∣ x + i.1 := by
  classical
  let residue : Fin k → ℕ := fun i ↦ m i - i.1 % m i
  have hm0 : ∀ i ∈ (Finset.univ : Finset (Fin k)), m i ≠ 0 := by
    intro i _
    have := hm i
    omega
  have hpairSet : Set.Pairwise
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun i j ↦ Nat.Coprime (m i) (m j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let y := Nat.chineseRemainderOfFinset residue m Finset.univ hm0 hpairSet
  let P := ∏ i : Fin k, m i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ ↦ by have := hm i; omega
  let x := (y : ℕ) % P + P
  have hmodLt : (y : ℕ) % P < P := Nat.mod_lt _ hPpos
  refine ⟨x, ?_, ?_, fun i ↦ ?_⟩
  · dsimp [x, P]
    omega
  · dsimp [x, P] at hmodLt ⊢
    omega
  · have hy : (y : ℕ) ≡ residue i [MOD m i] :=
      y.property i (Finset.mem_univ i)
    have hmP : m i ∣ P := by
      dsimp [P]
      simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hyP : (y : ℕ) % P ≡ (y : ℕ) [MOD m i] :=
      (Nat.mod_modEq (y : ℕ) P).of_dvd hmP
    have hremLt : i.1 % m i < m i := Nat.mod_lt _ (by have := hm i; omega)
    have hresidueDvd : m i ∣ residue i + i.1 := by
      refine ⟨i.1 / m i + 1, ?_⟩
      dsimp [residue]
      calc
        m i - i.1 % m i + i.1 =
            m i - i.1 % m i + (i.1 % m i + m i * (i.1 / m i)) := by
              rw [Nat.mod_add_div]
        _ = m i + m i * (i.1 / m i) := by omega
        _ = m i * (i.1 / m i + 1) := by ring
    have hcong : (y : ℕ) % P + i.1 ≡ residue i + i.1 [MOD m i] :=
      (hyP.trans hy).add_right i.1
    have hyDvd : m i ∣ (y : ℕ) % P + i.1 :=
      Nat.modEq_zero_iff_dvd.mp
        (hcong.trans (Nat.modEq_zero_iff_dvd.mpr hresidueDvd))
    have hx : x + i.1 = ((y : ℕ) % P + i.1) + P := by
      dsimp [x]
      omega
    rw [hx]
    exact dvd_add hyDvd hmP

/-! ## Persistence of common divisors -/

private theorem baseline_lt_block_product {B : ℕ} (m : Fin B → ℕ)
    (hm : ∀ i, B < m i) : B < ∏ i, m i := by
  by_cases hB : B = 0
  · subst B
    simp
  · have hBpos : 0 < B := by omega
    let i : Fin B := ⟨0, hBpos⟩
    have hprodpos : 0 < ∏ j, m j :=
      Finset.prod_pos (fun j _ => lt_of_le_of_lt (Nat.zero_le B) (hm j))
    have hdiv : m i ∣ ∏ j, m j := by
      simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    exact (hm i).trans_le (Nat.le_of_dvd hprodpos hdiv)

theorem solution {B : ℕ} (m : Fin B → ℕ)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x, B < (∏ i, m i) ∧ (∏ i, m i) ≤ x ∧ x < 2 * ∏ i, m i ∧
      ∀ L : ℤ, (∀ i, (m i : ℤ) ∣ L) → ∀ k : ℕ, ∀ z : ℤ,
        (x + B + k * (∏ i, m i) : ℕ) - (B : ℤ) ≤ z →
        z < (x + B + k * (∏ i, m i) : ℕ) →
        ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by
  have hm1 : ∀ i, 1 < m i := by
    intro i
    have := i.isLt
    have := hm i
    omega
  obtain ⟨x, hxlo, hxhi, hresidue⟩ :=
    exists_consecutiveMultiples_between m hm1 hpair
  refine ⟨x, baseline_lt_block_product m hm, hxlo, hxhi, ?_⟩
  intro L hL k
  exact covering_of_crt_block m x (∏ i, m i) k L hm
    (fun i => by simpa using Finset.dvd_prod_of_mem m (Finset.mem_univ i)) hL hresidue
