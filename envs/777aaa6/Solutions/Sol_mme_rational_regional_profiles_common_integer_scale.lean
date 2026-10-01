-- Prove2me | solution 1 for mme_rational_regional_profiles_common_integer_scale
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T20:02:51.836802+00:00
-- url     : https://prove2.me/submissions/65b2d44e-a934-41b8-b831-1668378cbe1f

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Clear a finite family of nonnegative rational denominators simultaneously. -/
private theorem common_natural_scale {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : I → ℕ, ∀ i, (a i : ℚ) = D * q i := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ ↦ (q i).den_pos)
  have hd (i : I) : (q i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨D, hD, fun i ↦ (D / (q i).den) * (q i).num.toNat, ?_⟩
  intro i
  have hnum : ((q i).num.toNat : ℚ) = ((q i).num : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))]
  have hmul : (D / (q i).den : ℕ) * (q i).den = D := Nat.div_mul_cancel (hd i)
  have hmulQ : ((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ) = (D : ℚ) := by
    exact_mod_cast hmul
  have hden : ((q i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
  have hnumQ : ((q i).num : ℚ) = q i * ((q i).den : ℚ) :=
    (div_eq_iff hden).mp (Rat.num_div_den (q i))
  calc
    _ = ((D / (q i).den : ℕ) : ℚ) * ((q i).num : ℚ) := by rw [Nat.cast_mul, hnum]
    _ = (((D / (q i).den : ℕ) : ℚ) * ((q i).den : ℚ)) * q i := by rw [hnumQ]; ring
    _ = _ := by rw [hmulQ]

/-- A single denominator realizes all regional and child counts, preserving
the exact linear compatibility equations at every positive square scale. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W]
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (N : Fin R → ℚ) (hN : ∀ r, 0 < N r)
    (M : ∀ r, RecursiveThinSplit.Split half (parent r) → ℚ) (hM : ∀ r s, 0 ≤ M r s)
    (U : Fin 3 → Cell half R parent → W → ℚ) (hU : ∀ i s w, 0 ≤ U i s w)
    (hm : ∀ r, ∑ s, M r s = N r)
    (hu : ∀ i s, ∑ w, U i s w = M s.1 s.2 + M s.1 (complement (htotal s.1) s.2)) :
    ∃ D : ℕ, 0 < D ∧ ∃ n : Fin R → ℕ,
      ∃ m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ,
      ∃ mu : Fin 3 → Cell half R parent → W → ℕ,
      (∀ r, (n r : ℚ) = D * N r) ∧
      (∀ r s, (m r s : ℚ) = D * M r s) ∧
      (∀ i s w, (mu i s w : ℚ) = D * U i s w) ∧
      (∀ r, 0 < n r) ∧
      ∀ k : ℕ, 0 < k →
        (∀ r, 0 < k ^ 2 * n r) ∧
        (∀ r, ∑ s, k ^ 2 * m r s = k ^ 2 * n r) ∧
        (∀ i s, ∑ w, k ^ 2 * mu i s w =
          k ^ 2 * m s.1 s.2 + k ^ 2 * m s.1 (complement (htotal s.1) s.2)) := by
  classical
  let I := Sum (Fin R) (Sum ((r : Fin R) × RecursiveThinSplit.Split half (parent r))
    (Fin 3 × Cell half R parent × W))
  let q : I → ℚ := fun x ↦ match x with
    | .inl r => N r
    | .inr (.inl s) => M s.1 s.2
    | .inr (.inr s) => U s.1 s.2.1 s.2.2
  have hq : ∀ x, 0 ≤ q x := by
    intro x
    cases x with
    | inl r => exact (hN r).le
    | inr s =>
      cases s with
      | inl s => exact hM s.1 s.2
      | inr s => exact hU s.1 s.2.1 s.2.2
  obtain ⟨D, hD, a, ha⟩ := common_natural_scale q hq
  let n : Fin R → ℕ := fun r ↦ a (.inl r)
  let m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ :=
    fun r s ↦ a (.inr (.inl ⟨r,s⟩))
  let mu : Fin 3 → Cell half R parent → W → ℕ :=
    fun i s w ↦ a (.inr (.inr ⟨i,s,w⟩))
  have hnq : ∀ r, (n r : ℚ) = D * N r := fun r ↦ ha (.inl r)
  have hmq : ∀ r s, (m r s : ℚ) = D * M r s := fun r s ↦ ha (.inr (.inl ⟨r,s⟩))
  have huq : ∀ i s w, (mu i s w : ℚ) = D * U i s w :=
    fun i s w ↦ ha (.inr (.inr ⟨i,s,w⟩))
  have hn : ∀ r, 0 < n r := by
    intro r
    have : 0 < (n r : ℚ) := by rw [hnq r]; exact mul_pos (Nat.cast_pos.mpr hD) (hN r)
    exact_mod_cast this
  have hmn : ∀ r, ∑ s, m r s = n r := by
    intro r
    apply Nat.cast_injective (R := ℚ)
    simp only [Nat.cast_sum, hmq, hnq, ← Finset.mul_sum, hm]
  have hun : ∀ i s, ∑ w, mu i s w = m s.1 s.2 + m s.1 (complement (htotal s.1) s.2) := by
    intro i s
    apply Nat.cast_injective (R := ℚ)
    simp only [Nat.cast_sum, Nat.cast_add, huq, hmq, ← Finset.mul_sum, hu, mul_add]
  refine ⟨D, hD, n, m, mu, hnq, hmq, huq, hn, ?_⟩
  intro k hk
  refine ⟨fun r ↦ Nat.mul_pos (pow_pos hk _) (hn r), ?_, ?_⟩
  · intro r
    rw [← Finset.mul_sum, hmn r]
  · intro i s
    rw [← Finset.mul_sum, hun i s, mul_add]

