-- Prove2me | solution 1 for TropicalLA.exists_critical_node
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T08:46:55.608183+00:00
-- url     : https://prove2.me/submissions/2c842625-2a45-47f3-a351-d02ac4171ece

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ) :
    ∃ (q : ℕ) (z : ι), 0 < q ∧ q ≤ Fintype.card ι ∧
      ∀ k : ℕ, 0 < k → ((k * q : ℕ) : ℝ) * maxCycleMean A ≤ tpow A (k * q - 1) z z := by
  classical
  have hstep : ∀ m i t, tpow A (m + 1) i t
      = univ.sup' univ_nonempty (fun l => tpow A m i l + A l t) := fun _ _ _ => rfl
  -- concatenating optimal walks
  have hsuper : ∀ b a i l j, tpow A a i l + tpow A b l j ≤ tpow A (a + b + 1) i j := by
    intro b
    induction b with
    | zero =>
      intro a i l j
      show tpow A a i l + A l j ≤ tpow A (a + 1) i j
      rw [hstep a i j]
      exact Finset.le_sup' (fun l' => tpow A a i l' + A l' j) (mem_univ l)
    | succ b ih =>
      intro a i l j
      obtain ⟨l', -, hl'⟩ := Finset.exists_mem_eq_sup' univ_nonempty
        (fun l' => tpow A b l l' + A l' j)
      have h3 : tpow A (b + 1) l j = tpow A b l l' + A l' j := by rw [hstep b l j, hl']
      have h4 : tpow A (a + (b + 1) + 1) i j
          = univ.sup' univ_nonempty (fun l'' => tpow A (a + b + 1) i l'' + A l'' j) := by
        rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega]
        exact hstep (a + b + 1) i j
      have h1 := ih a i l l'
      have h2 := Finset.le_sup' (fun l'' => tpow A (a + b + 1) i l'' + A l'' j) (mem_univ l')
      rw [h3, h4]
      linarith
  -- a critical cycle
  obtain ⟨⟨k0, z⟩, hkz, hmu⟩ := Finset.exists_mem_eq_sup' (cycleIndex_nonempty (ι := ι))
    (fun q : ℕ × ι => tpow A q.1 q.2 q.2 / ((q.1 : ℝ) + 1))
  have hmu' : maxCycleMean A = tpow A k0 z z / ((k0 : ℝ) + 1) := hmu
  have hk0 : k0 < Fintype.card ι := Finset.mem_range.1 (Finset.mem_product.1 hkz).1
  have hcrit : tpow A k0 z z = ((k0 : ℝ) + 1) * maxCycleMean A := by
    have hk1 : (k0 : ℝ) + 1 ≠ 0 := by positivity
    rw [hmu']
    field_simp
  refine ⟨k0 + 1, z, by omega, by omega, ?_⟩
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [show (0 + 1) * (k0 + 1) - 1 = k0 by omega, hcrit]
      apply le_of_eq
      push_cast
      ring
    · have h1 := ih h0
      have h2 := hsuper k0 (k * (k0 + 1) - 1) z z z
      have hkq : 1 ≤ k * (k0 + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      have hmul : (k + 1) * (k0 + 1) = k * (k0 + 1) + k0 + 1 := by ring
      rw [show k * (k0 + 1) - 1 + k0 + 1 = (k + 1) * (k0 + 1) - 1 by omega] at h2
      rw [hcrit] at h2
      have hcast : (((k + 1) * (k0 + 1) : ℕ) : ℝ) = ((k * (k0 + 1) : ℕ) : ℝ) + k0 + 1 := by
        rw [hmul]
        push_cast
        ring
      rw [hcast]
      linarith
