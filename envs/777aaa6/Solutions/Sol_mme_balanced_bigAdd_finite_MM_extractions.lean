-- Prove2me | solution 1 for mme_balanced_bigAdd_finite_MM_extractions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:09:36.054617+00:00
-- url     : https://prove2.me/submissions/7b1fe5a3-53a1-4b6a-ac73-c7fcd3fe447a

import Theorems.Thm_mme_balanced_bigAdd_power_type_restrict
import Theorems.Thm_mme_finite_MM_extractions_kronFin_replicate

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    {n r V : ℕ} (X : Fin n → TensorObj K 3)
    (L : ℝ) (hn : 0 < n) (hL : 0 ≤ L)
    (hextract : ∀ p : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((X p).kronPow r) ∧
        L ≤ (k : ℝ) ∧
        (∀ i, a i * b i * c i = V)) :
    let R : ℕ := n * r
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((TensorObj.bigAdd X).kronPow R) ∧
      (W : ℝ) * L ^ n ≤ (k : ℝ) ∧
      (∀ i, a i * b i * c i = V ^ n) := by
  dsimp only
  let R : ℕ := n * r
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin n // ∀ p,
        Fintype.card {j // w j = p} = r}
  let Y : Fin n → TensorObj K 3 := fun p => (X p).kronPow r
  obtain ⟨k, a, b, c, hrestrict, hk, hvolume⟩ :=
    mme_finite_MM_extractions_kronFin_replicate
      (W := W) Y L hn hL (by simpa [Y] using hextract)
  refine ⟨k, a, b, c, ?_, ?_, hvolume⟩
  · exact TensorObj.Restrict.trans hrestrict
      (by simpa [R, W, Y] using
        mme_balanced_bigAdd_power_type_restrict X hn)
  · simpa [W] using hk
