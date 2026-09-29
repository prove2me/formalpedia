-- Prove2me | solution 1 for mme_finite_word_family_histogram_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:04:10.265037+00:00
-- url     : https://prove2.me/submissions/0c3d49e3-7e6a-4398-ad94-8bad524b8200

import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.FiniteHistogramEntropy

private theorem prescribed_word_card
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (q : B → ℕ) (hsum : ∑ b, q b = Fintype.card A) :
    Nat.card {f : A → B //
        ∀ b, Fintype.card {a // f a = b} = q b} =
      Nat.multinomial Finset.univ q := by
  rw [Nat.card_eq_fintype_card,
    mme_fintype_prescribed_fiber_function_card q hsum,
    Nat.multinomial, hsum]

theorem proof
    {R : Type*} [Fintype R] [DecidableEq R]
    (n : ℕ) (hn : 0 < n)
    (F : Finset (Fin n → R)) (H : ℝ)
    (hH : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦ (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)) ≤ H) :
    (F.card : ℝ) ≤
      (((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        Real.exp ((n : ℝ) * Real.log 2 * H) := by
  classical
  let histogram : (Fin n → R) → (R → Fin (n + 1)) := fun f r ↦
    ⟨Fintype.card {t : Fin n // f t = r},
      Nat.lt_succ_of_le (by
        simpa only [Fintype.card_fin] using
          (Fintype.card_subtype_le (fun t : Fin n ↦ f t = r)))⟩
  have hFiberBound (q : R → Fin (n + 1)) :
      ((F.filter fun f ↦ histogram f = q).card : ℝ) ≤
        Real.exp ((n : ℝ) * Real.log 2 * H) := by
    by_cases hne : (F.filter fun f ↦ histogram f = q).Nonempty
    · let f := hne.choose
      have hf : f ∈ F.filter fun g ↦ histogram g = q := hne.choose_spec
      have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
      have hfq : histogram f = q := (Finset.mem_filter.mp hf).2
      let counts : R → ℕ := fun r ↦ (q r).val
      have hhist (r : R) :
          counts r = Fintype.card {t : Fin n // f t = r} := by
        have hqr := congrFun hfq r
        exact congrArg Fin.val hqr.symm
      have hsum : ∑ r, counts r = n := by
        calc
          ∑ r, counts r =
              ∑ r, Fintype.card {t : Fin n // f t = r} := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hhist r
          _ = Fintype.card (Σ r : R, {t : Fin n // f t = r}) :=
            Fintype.card_sigma.symm
          _ = Fintype.card (Fin n) :=
            Fintype.card_congr (Equiv.sigmaFiberEquiv f)
          _ = n := Fintype.card_fin n
      have hsumPos : 0 < ∑ r, counts r := by simpa [hsum] using hn
      let AllWords := {g : Fin n → R //
        ∀ r, Fintype.card {t // g t = r} = counts r}
      let forget : {g // g ∈ F.filter fun f ↦ histogram f = q} →
          AllWords := fun g ↦ ⟨g.1, fun r ↦ by
            have hqr := congrFun (Finset.mem_filter.mp g.2).2 r
            exact congrArg Fin.val hqr⟩
      have hforget : Function.Injective forget := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun x : AllWords ↦ x.1) hab
      have hCardLe :
          (F.filter fun f ↦ histogram f = q).card ≤ Nat.card AllWords := by
        have h := Nat.card_le_card_of_injective forget hforget
        simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
      have hAllWords : Nat.card AllWords =
          Nat.multinomial Finset.univ counts :=
        prescribed_word_card counts (by simpa using hsum)
      have hMultinomial := mme_dwz_multinomial_entropy_upper
        counts 1 (by norm_num) hsumPos
      have hEntropy :
          mme_modern_entropyBits
              (fun r ↦ (counts r : ℝ) / (n : ℝ)) ≤ H := by
        simpa only [hhist] using hH f hfF
      have hExp :
          Real.exp ((n : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (fun r ↦ (counts r : ℝ) / (n : ℝ))) ≤
            Real.exp ((n : ℝ) * Real.log 2 * H) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hEntropy (by positivity)
      calc
        ((F.filter fun f ↦ histogram f = q).card : ℝ) ≤
            (Nat.card AllWords : ℝ) := by exact_mod_cast hCardLe
        _ = (Nat.multinomial Finset.univ counts : ℝ) := by rw [hAllWords]
        _ ≤ Real.exp ((n : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (fun r ↦ (counts r : ℝ) / (n : ℝ))) := by
          simpa [hsum] using hMultinomial
        _ ≤ Real.exp ((n : ℝ) * Real.log 2 * H) := hExp
    · have hzero : (F.filter fun f ↦ histogram f = q).card = 0 :=
        Finset.not_nonempty_iff_eq_empty.mp hne ▸ rfl
      rw [hzero]
      simpa only [Nat.cast_zero] using (Real.exp_pos _).le
  have hPartition : F.card =
      ∑ q : R → Fin (n + 1),
        (F.filter fun f ↦ histogram f = q).card := by
    calc
      F.card = ∑ f ∈ F, 1 := by simp
      _ = ∑ q : R → Fin (n + 1),
          ∑ f ∈ F with histogram f = q, 1 :=
        (Finset.sum_fiberwise F histogram (fun _ ↦ 1)).symm
      _ = ∑ q : R → Fin (n + 1),
          (F.filter fun f ↦ histogram f = q).card := by simp
  rw [hPartition, Nat.cast_sum]
  calc
    ∑ q : R → Fin (n + 1),
        ((F.filter fun f ↦ histogram f = q).card : ℝ) ≤
        ∑ _q : R → Fin (n + 1),
          Real.exp ((n : ℝ) * Real.log 2 * H) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hFiberBound q
    _ = (Fintype.card (R → Fin (n + 1)) : ℝ) *
        Real.exp ((n : ℝ) * Real.log 2 * H) := by simp
    _ = (((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        Real.exp ((n : ℝ) * Real.log 2 * H) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      norm_num

end MME.FiniteHistogramEntropy

theorem solution
    {R : Type*} [Fintype R] [DecidableEq R]
    (n : ℕ) (hn : 0 < n)
    (F : Finset (Fin n → R)) (H : ℝ)
    (hH : ∀ f ∈ F,
      mme_modern_entropyBits
          (fun r ↦ (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)) ≤ H) :
    (F.card : ℝ) ≤
      (((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        Real.exp ((n : ℝ) * Real.log 2 * H) :=
  MME.FiniteHistogramEntropy.proof n hn F H hH
