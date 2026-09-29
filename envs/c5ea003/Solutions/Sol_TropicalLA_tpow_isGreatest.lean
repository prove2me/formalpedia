-- Prove2me | solution 1 for TropicalLA.tpow_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:25.037337+00:00
-- url     : https://prove2.me/submissions/9d52d129-6103-4688-b630-2a00d4aa2ced

-- Sol generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_exists_tmul_eq
import Theorems.Thm_TropicalLA_le_tmul
/-
# Tropical (max-plus) matrices with finite entries

For matrices with entries in `ℝ` (i.e. no `-∞` entries) tropical multiplication is

  `(A ⊗ B) i j = max_k (A i k + B k j)`,

implemented with `Finset.sup'`.  We prove

* `tmul_assoc` : tropical matrix multiplication is associative (a hands-on proof,
  independent of the semiring instance);
* `tmul_embed`  : this operation agrees with multiplication in `Matrix ι ι (MaxPlus ℝ)`,
  so the two developments are coherent;
* `tpow_isGreatest` : **max-plus powers compute optimal paths** — the `(i,j)` entry of
  `A^{⊗(m+1)}` is the maximal weight of a length-`(m+1)` walk from `i` to `j`
  (the algebraic form of the Bellman dynamic-programming principle).
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]





















open TropicalLA in
theorem solution(A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    IsGreatest {w : ℝ | ∃ p : ℕ → ι, p 0 = i ∧ p (m + 1) = j ∧ w = pathWeight A p (m + 1)}
      (tpow A m i j) := by
  induction m generalizing i j with
  | zero =>
      constructor
      · refine ⟨fun t => if t = 0 then i else j, by simp, by simp, ?_⟩
        simp [pathWeight, tpow]
      · rintro w ⟨p, hp0, hp1, rfl⟩
        simp [pathWeight, hp0, hp1, tpow]
  | succ m ih =>
      constructor
      · obtain ⟨k, hk⟩ := exists_tmul_eq (tpow A m) A i j
        obtain ⟨p, hp0, hpm, hpw⟩ := (ih i k).1
        refine ⟨fun t => if t ≤ m + 1 then p t else j, by simpa using hp0, by simp, ?_⟩
        have hsum : ∑ t ∈ Finset.range (m + 1),
            A ((fun t => if t ≤ m + 1 then p t else j) t)
              ((fun t => if t ≤ m + 1 then p t else j) (t + 1)) = pathWeight A p (m + 1) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [Finset.mem_range] at ht
          have h1 : t ≤ m + 1 := by omega
          have h2 : t + 1 ≤ m + 1 := by omega
          simp [h1, h2]
        show tpow A (m + 1) i j = pathWeight A _ (m + 2)
        rw [pathWeight, Finset.sum_range_succ, hsum]
        have hlt : ¬ (m + 2 ≤ m + 1) := by omega
        simp only [hlt, if_false, le_refl, if_true]
        rw [hpm] at *
        show tmul (tpow A m) A i j = _
        rw [hk, ← hpw]
      · rintro w ⟨p, hp0, hpm, rfl⟩
        rw [pathWeight, Finset.sum_range_succ]
        have h1 : ∑ t ∈ Finset.range (m + 1), A (p t) (p (t + 1)) ≤ tpow A m i (p (m + 1)) :=
          (ih i (p (m + 1))).2 ⟨p, hp0, rfl, rfl⟩
        have h2 : tpow A m i (p (m + 1)) + A (p (m + 1)) j ≤ tmul (tpow A m) A i j :=
          le_tmul (tpow A m) A i j (p (m + 1))
        have h3 : A (p (m + 1)) (p (m + 2)) = A (p (m + 1)) j := by rw [hpm]
        show _ ≤ tmul (tpow A m) A i j
        rw [h3]
        linarith
