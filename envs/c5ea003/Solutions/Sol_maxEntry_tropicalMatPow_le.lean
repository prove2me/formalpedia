-- Prove2me | solution 1 for maxEntry_tropicalMatPow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:21.750096+00:00
-- url     : https://prove2.me/submissions/f0136bce-cc4b-40c1-92e6-dd15fbae1feb

-- Sol generated from Bridges/NeuralCoding/MaxPlusLemmas.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_MaxPlusDefs

/-!
# Max-Plus Algebra: Structural Lemmas

Basic structural properties of max-plus matrix operations.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}


/-- Recurrence: `M^(k+1) = tropicalMatMul M (M^k)`. -/
theorem tropicalMatPow_succ (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    tropicalMatPow hn M (k + 1) = tropicalMatMul hn M (tropicalMatPow hn M k) := by
  rfl




/-- Max entry is ≥ any individual entry. -/
theorem le_maxEntry (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    M i j ≤ maxEntry hn M := by
  unfold maxEntry
  exact le_trans (Finset.le_sup' _ (Finset.mem_univ j))
    (Finset.le_sup' (fun i => Finset.sup' Finset.univ _ fun j => M i j)
      (Finset.mem_univ i))


/-
The diagonal entry `(M^k) i i ≥ k * M i i` (by self-loop path).
-/

/-
Every entry of the tropical product is at most `maxEntry A + maxEntry B`.
-/
theorem tropicalMatMul_entry_le (hn : 0 < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    tropicalMatMul hn A B i j ≤ maxEntry hn A + maxEntry hn B := by
  exact Finset.sup'_le _ _ fun x _ => add_le_add ( le_maxEntry hn A i x ) ( le_maxEntry hn B x j )

/-
Max entry of `M^k` is bounded by `k * maxEntry M` for `k ≥ 1`.
-/


theorem solution(hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k) :
    maxEntry hn (tropicalMatPow hn M k) ≤ k * maxEntry hn M := by
  -- By the induction hypothesis, we have `maxEntry (tropicalMatPow hn M k) ≤ k * maxEntry hn M`.
  have h_ind : ∀ k : ℕ, 1 ≤ k → maxEntry hn (tropicalMatPow hn M k) ≤ k * maxEntry hn M := by
    intro k hk
    induction' k, Nat.succ_le_iff.mpr hk using Nat.le_induction with k ih;
    · simp +decide [ tropicalMatPow_succ, tropicalMatMul ];
      unfold maxEntry tropicalMatMul tropicalMatPow; norm_num;
    · -- By the properties of the maxEntry function, we have:
      have h_maxEntry_mul : maxEntry hn (tropicalMatPow hn M (k + 1)) ≤ maxEntry hn M + maxEntry hn (tropicalMatPow hn M k) := by
        exact Finset.sup'_le _ _ fun i hi => Finset.sup'_le _ _ fun j hj => by simpa using tropicalMatMul_entry_le hn M ( tropicalMatPow hn M k ) i j;
      grind +splitImp;
  exact_mod_cast h_ind _ hk
