-- Prove2me | solution 1 for ReweightedNPMLE.augmented_linearIndepOn_of_finiteMixtureFiber_extreme
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:52:49.96235+00:00
-- url     : https://prove2.me/submissions/1cbe071f-092d-4c7b-a7ad-2f4e81521d73

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber

-- Inline helpers preserved from ReweightedNPMLE.FiniteOptimizerFiber.
section
/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE























@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
  simp [coefficientSupport]



























end ReweightedNPMLE
end

/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Conversely, every extreme point of a finite probability-mixture fiber has
an affinely independent active dictionary. -/
theorem solution
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m)) := by
  classical
  let S := coefficientSupport p
  rw [linearIndepOn_finset_iff]
  intro f hf
  by_contra hcoeff
  push Not at hcoeff
  obtain ⟨i₀, hi₀S, hi₀⟩ := hcoeff
  have hpFiber : p ∈ finiteMixtureFiber A v := hp.1
  have hSnonempty : S.Nonempty := ⟨i₀, hi₀S⟩
  let P : Finset ℝ := S.image p
  have hPnonempty : P.Nonempty := hSnonempty.image p
  let δ : ℝ := P.min' hPnonempty
  have hδmem : δ ∈ P := Finset.min'_mem P hPnonempty
  have hδpos : 0 < δ := by
    rcases Finset.mem_image.mp hδmem with ⟨i, hiS, hiδ⟩
    rw [← hiδ]
    exact lt_of_le_of_ne (hpFiber.1.1 i)
      (mem_coefficientSupport p i |>.mp hiS).symm
  have hδle (i : Fin m) (hiS : i ∈ S) : δ ≤ p i := by
    exact Finset.min'_le P (p i) (Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
  let M : ℝ := ∑ i ∈ S, |f i|
  have hMnonneg : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  let ε : ℝ := δ / (2 * (M + 1))
  have hdenpos : 0 < 2 * (M + 1) := mul_pos (by norm_num) (by linarith)
  have hεpos : 0 < ε := div_pos hδpos hdenpos
  let c : Fin m → ℝ := fun i ↦ if i ∈ S then f i else 0
  have hc_eq (i : Fin m) (hiS : i ∈ S) : c i = f i := by simp [c, hiS]
  have hc_zero (i : Fin m) (hiS : i ∉ S) : c i = 0 := by simp [c, hiS]
  have hc_aug : ∑ i : Fin m, c i • augmentedDictionary A i = 0 := by
    have hfull : (∑ i : Fin m, c i • augmentedDictionary A i) =
        ∑ i ∈ S, c i • augmentedDictionary A i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hiS
      rw [hc_zero i hiS, zero_smul]
    rw [hfull]
    calc
      (∑ i ∈ S, c i • augmentedDictionary A i) =
          ∑ i ∈ S, f i • augmentedDictionary A i := by
        apply Finset.sum_congr rfl
        intro i hiS
        rw [hc_eq i hiS]
      _ = 0 := by simpa [S] using hf
  have hc_sum : ∑ i : Fin m, c i = 0 := by
    have hfirst := congrArg (AddMonoidHom.fst ℝ E) hc_aug
    simpa [augmentedDictionary] using hfirst
  have hc_value : ∑ i : Fin m, c i • A i = 0 := by
    have hsecond := congrArg (AddMonoidHom.snd ℝ E) hc_aug
    simpa [augmentedDictionary] using hsecond
  have hc_bound (i : Fin m) : |ε * c i| ≤ p i := by
    by_cases hiS : i ∈ S
    · have hfi_le : |f i| ≤ M := by
        exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (f j)) hiS
      have hfi_den : |f i| ≤ 2 * (M + 1) := by linarith
      have heq : ε * (2 * (M + 1)) = δ := by
        dsimp [ε]
        field_simp
      calc
        |ε * c i| = ε * |f i| := by
          rw [hc_eq i hiS, abs_mul, abs_of_pos hεpos]
        _ ≤ ε * (2 * (M + 1)) := mul_le_mul_of_nonneg_left hfi_den hεpos.le
        _ = δ := heq
        _ ≤ p i := hδle i hiS
    · rw [hc_zero i hiS, mul_zero, abs_zero]
      exact hpFiber.1.1 i
  let q : Fin m → ℝ := fun i ↦ p i + ε * c i
  let r : Fin m → ℝ := fun i ↦ p i - ε * c i
  have hqnonneg (i : Fin m) : 0 ≤ q i := by
    have h := (abs_le.mp (hc_bound i)).1
    dsimp [q]
    linarith
  have hrnonneg (i : Fin m) : 0 ≤ r i := by
    have h := (abs_le.mp (hc_bound i)).2
    dsimp [r]
    linarith
  have hqsum : ∑ i : Fin m, q i = 1 := by
    simp only [q, Finset.sum_add_distrib, ← Finset.mul_sum, hc_sum, mul_zero, add_zero,
      hpFiber.1.2]
  have hrsum : ∑ i : Fin m, r i = 1 := by
    simp only [r, Finset.sum_sub_distrib, ← Finset.mul_sum, hc_sum, mul_zero, sub_zero,
      hpFiber.1.2]
  have hqvalue : finiteMixtureValue A q = v := by
    calc
      finiteMixtureValue A q = finiteMixtureValue A p + ε • (∑ i, c i • A i) := by
        simp [finiteMixtureValue, q, add_smul, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul]
      _ = v := by rw [hc_value, smul_zero, add_zero, hpFiber.2]
  have hrvalue : finiteMixtureValue A r = v := by
    calc
      finiteMixtureValue A r = finiteMixtureValue A p - ε • (∑ i, c i • A i) := by
        simp [finiteMixtureValue, r, sub_smul, Finset.sum_sub_distrib,
          Finset.smul_sum, smul_smul]
      _ = v := by rw [hc_value, smul_zero, sub_zero, hpFiber.2]
  have hqFiber : q ∈ finiteMixtureFiber A v := ⟨⟨hqnonneg, hqsum⟩, hqvalue⟩
  have hrFiber : r ∈ finiteMixtureFiber A v := ⟨⟨hrnonneg, hrsum⟩, hrvalue⟩
  have hqne : q ≠ p := by
    intro hqp
    have hi := congrFun hqp i₀
    have hc0 : c i₀ = f i₀ := hc_eq i₀ hi₀S
    dsimp [q] at hi
    rw [hc0] at hi
    have : ε * f i₀ ≠ 0 := mul_ne_zero hεpos.ne' hi₀
    apply this
    linarith
  have hpseg : p ∈ openSegment ℝ q r := by
    rw [openSegment_eq_image]
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    funext i
    dsimp [q, r]
    ring
  exact hqne (hp.2 hqFiber hrFiber hpseg)
