-- Prove2me | solution 1 for Catalog.Combinatorics.RotaBasis.cross_pairing_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:19.581399+00:00
-- url     : https://prove2.me/submissions/0d9e76b0-42c8-4861-97e9-912d7bba7e72

-- Sol generated from Combinatorics/RotaBasisSmallRanks.lean
import Mathlib
import Definitions.Def_Combinatorics_RotaBasisSmallRanks

/-!
# Rota's basis conjecture in ranks one and two

Rota's basis conjecture is open in full generality.  This file gives a faithful
formalization using Mathlib's `Basis` and proves the conjecture for one and two
bases.  An arrangement records that every row is a permutation of the given
basis and that every column is linearly independent.  Since the columns have
exactly as many entries as the ambient dimension, `columnBasis` upgrades each
column to a Mathlib `Basis`.
-/

open Catalog.Combinatorics.RotaBasis

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]








open Catalog.Combinatorics.RotaBasis in
theorem solution(a b c d : V)
    (hab : LinearIndependent K (![a, b] : Fin 2 → V))
    (hcd : LinearIndependent K (![c, d] : Fin 2 → V)) :
    (LinearIndependent K (![a, c] : Fin 2 → V) ∧
      LinearIndependent K (![b, d] : Fin 2 → V)) ∨
    (LinearIndependent K (![a, d] : Fin 2 → V) ∧
      LinearIndependent K (![b, c] : Fin 2 → V)) := by
  rw [LinearIndependent.pair_iff] at hab hcd
  simp only [LinearIndependent.pair_iff]
  by_cases hac : ∀ (s t : K), s • a + t • c = 0 → s = 0 ∧ t = 0
  · by_cases hbd : ∀ (s t : K), s • b + t • d = 0 → s = 0 ∧ t = 0
    · left; exact ⟨hac, hbd⟩
    · right
      -- b, d are NOT linearly independent, so d = m • b for some m
      push_neg at hbd
      obtain ⟨s, t, hst, hst_ne⟩ := hbd
      by_cases ht : t = 0
      · -- If t = 0, then s • b = 0 with s ≠ 0, so b = 0
        subst ht
        simp at hst hst_ne
        -- hst : s = 0 ∨ b = 0, hst_ne : s ≠ 0
        rcases hst with hs | hb
        · exact False.elim (hst_ne hs)
        · -- b = 0 contradicts hab: 0 • a + 1 • b = 0 but 1 ≠ 0
          specialize hab 0 1
          simp [hb] at hab
      · -- t ≠ 0, so d = (-t⁻¹ * s) • b
        let m : K := -t⁻¹ * s
        have hd_eq : d = m • b := by
          have hst' : t • d = -(s • b) := eq_neg_of_add_eq_zero_right hst
          calc d = t⁻¹ • (t • d) := by rw [inv_smul_smul₀ ht]
            _ = t⁻¹ • -(s • b) := by rw [hst']
            _ = t⁻¹ • (-s • b) := by rw [neg_smul]
            _ = (t⁻¹ * -s) • b := by rw [smul_smul]
            _ = m • b := by simp [m, mul_neg]
        -- m ≠ 0, otherwise d = 0 contradicts hcd
        have hm_ne : m ≠ 0 := by
          intro hm_zero
          rw [hm_zero, zero_smul] at hd_eq
          specialize hcd 0 1
          simp [hd_eq] at hcd
        constructor
        · -- Prove (a, d) are linearly independent
          intro u v huv
          rw [hd_eq, smul_smul] at huv
          have := hab u (v * m) huv
          exact ⟨this.1, Or.resolve_right (mul_eq_zero.mp this.2) hm_ne⟩
        · -- Prove (b, c) are linearly independent
          intro u v huv
          by_cases hv : v = 0
          · simp [hv] at huv
            rcases huv with hu | hb
            · exact ⟨hu, hv⟩
            · specialize hab 0 1; simp [hb] at hab
          · -- v ≠ 0, so c = n • b for some n
            let n : K := -v⁻¹ * u
            have hc_eq : c = n • b := by
              have huv' : v • c = -(u • b) := eq_neg_of_add_eq_zero_right huv
              calc c = v⁻¹ • (v • c) := by rw [inv_smul_smul₀ hv]
                _ = v⁻¹ • -(u • b) := by rw [huv']
                _ = v⁻¹ • (-u • b) := by rw [neg_smul]
                _ = (v⁻¹ * -u) • b := by rw [smul_smul]
                _ = n • b := by simp [n, mul_neg]
            -- Then (c, d) = (n • b, m • b) are lin.dep., contradicting hcd
            -- Use scalars s = m, t = -(m * n * m⁻¹)
            set mc := m * n with hmc
            specialize hcd m (-(mc * m⁻¹))
            rw [hc_eq, hd_eq, smul_smul, smul_smul] at hcd
            have h0 : (m * n) • b + (-(mc * m⁻¹) * m) • b = 0 := by
              have heq : (-(mc * m⁻¹) * m) = -mc := by
                rw [neg_mul, mul_assoc, inv_mul_cancel₀ hm_ne, mul_one]
              rw [heq, neg_smul]
              exact add_neg_cancel _
            have := hcd h0
            exact absurd this.1 hm_ne
  · right
    -- Case: a, c are NOT linearly independent
    -- Extract: ∃ s t, s • a + t • c = 0 ∧ ¬(s = 0 ∧ t = 0)
    push_neg at hac
    obtain ⟨s, t, hst, hst_ne⟩ := hac
    -- Case analysis on whether s = 0
    by_cases hs : s = 0
    · -- If s = 0, then t • c = 0 with t ≠ 0, so c = 0
      subst hs
      simp at hst hst_ne
      -- hst : t = 0 ∨ c = 0 and hst_ne : t ≠ 0
      rcases hst with ht | hc
      · exact absurd ht hst_ne
      · -- c = 0 contradicts hcd
        specialize hcd 1 0
        simp [hc] at hcd
    · -- If s ≠ 0, then c = -(s)⁻¹ • t • a = λ • a where λ = -(s⁻¹ * t)
      let k : K := -(s⁻¹ * t)
      have ha_eq : a = k • c := by
        have h1 : s • a = -(t • c) := by rw [add_eq_zero_iff_eq_neg] at hst; exact hst
        have h2 : a = s⁻¹ • (s • a) := by rw [inv_smul_smul₀ hs]
        rw [h2, h1]
        simp [k, smul_neg, smul_smul]
      -- k ≠ 0, otherwise a = 0 contradicts hab
      have hk_ne : k ≠ 0 := by
        intro hk_zero
        rw [hk_zero, zero_smul] at ha_eq
        -- a = 0 contradicts hab
        have := hab 1 0; simp [ha_eq] at this
      constructor
      · -- Prove (a, d) are linearly independent
        intro u v huv
        -- u • a + v • d = 0 becomes (u * k) • c + v • d = 0
        rw [ha_eq, smul_smul] at huv
        have := hcd (u * k) v huv
        exact ⟨Or.resolve_right (mul_eq_zero.mp this.1) hk_ne, this.2⟩
      · -- Prove (b, c) are linearly independent
        intro u v huv
        by_cases hv : v = 0
        · simp [hv] at huv
          rcases huv with hu | hb
          · exact ⟨hu, hv⟩
          · -- b = 0 contradicts hab
            specialize hab 0 1; simp [hb] at hab
        · -- v ≠ 0, so c = (-v⁻¹ * u) • b
          have hv_inv : v⁻¹ ≠ 0 := inv_ne_zero hv
          have hc_eq_b : c = (-v⁻¹ * u) • b := by
            have huv' : v • c = -(u • b) := eq_neg_of_add_eq_zero_right huv
            calc c = v⁻¹ • (v • c) := by rw [inv_smul_smul₀ hv]
              _ = v⁻¹ • -(u • b) := by rw [huv']
              _ = v⁻¹ • (-u • b) := by rw [neg_smul]
              _ = (-v⁻¹ * u) • b := by rw [smul_smul]; congr 1; simp [mul_neg]
          -- Then a = k • c = (k * (-v⁻¹ * u)) • b
          have ha_eq_b : a = (k * (-v⁻¹ * u)) • b := by rw [ha_eq, hc_eq_b, smul_smul]
          -- This contradicts hab
          specialize hab 1 (-(k * (-v⁻¹ * u)))
          rw [ha_eq_b] at hab
          simp at hab
