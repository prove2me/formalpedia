-- Prove2me | solution 1 for TropicalGraph.mpMul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:06:58.100658+00:00
-- url     : https://prove2.me/submissions/77414122-c609-4617-a4bd-6e77483855ad

-- Sol generated from Combinatorics/TropicalspectralgraphTheorems/TropicalSpectralGraph_Theorems.lean
import Mathlib
import Definitions.Def_Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs
import Definitions.Def_Combinatorics_TropicalspectralgraphTheorems_TropicalSpectralGraph_Theorems
import Theorems.Thm_TropicalEntropy_exists_ground_state
import Theorems.Thm_TropicalEntropy_le_tropSum
import Theorems.Thm_TropicalEntropy_tropSum_le

/-!
# Tropical spectral graph theory

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/TropicalSpectralGraph/Theorems.lean`.  It is
reconstructed here as a self-contained development of **min-plus (tropical) matrix
algebra** on a finite complete weighted digraph, the algebraic backbone of tropical
spectral graph theory: tropical matrix powers compute shortest walks, and the
tropical eigenvalue is a minimal cycle mean.

Main results:

* `TropicalGraph.mpMul` — the min-plus matrix product, together with
  `TropicalGraph.mpMul_assoc` (**associativity**, i.e. the Bellman optimality
  principle) and `TropicalGraph.mpMul_one` / `one_mpMul` (the tropical identity);
* `TropicalGraph.mpMul_le` — the shortest-walk upper bound `(A ⊗ B) i j ≤ A i k + B k j`;
* `TropicalGraph.mpMul_mono` — monotonicity in both arguments;
* `TropicalGraph.mpMul_shift` — the **spectral shift**: adding a constant `c` to all
  entries shifts every tropical eigenvalue by `c`;
* `TropicalGraph.mpPow_add` and `TropicalGraph.mpPow_le_mul` — the concatenation
  law for tropical powers, the input to Fekete's lemma for the minimal cycle mean.
-/

open TropicalGraph

open Finset TropicalEntropy

variable {n : ℕ} [NeZero n]




/-- The defining upper bound: every intermediate vertex gives an upper bound. -/
theorem mpMul_le (A B : Weighting n) (i j k : Fin n) : mpMul A B i j ≤ A i k + B k j :=
  tropSum_le (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin n)).Nonempty) _ (Finset.mem_univ k)

/-- The defining lower bound. -/
theorem le_mpMul (A B : Weighting n) (i j : Fin n) {c : ℝ}
    (h : ∀ k, c ≤ A i k + B k j) : c ≤ mpMul A B i j :=
  le_tropSum (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin n)).Nonempty) _ fun k _ => h k

/-- The minimum is attained. -/
theorem exists_mpMul_eq (A B : Weighting n) (i j : Fin n) :
    ∃ k, mpMul A B i j = A i k + B k j := by
  obtain ⟨k, -, hk⟩ := exists_ground_state (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin n)).Nonempty) (fun k => A i k + B k j)
  exact ⟨k, hk⟩













open TropicalGraph in
theorem solution(A B C : Weighting n) : mpMul (mpMul A B) C = mpMul A (mpMul B C) := by
  funext i j
  refine le_antisymm ?_ ?_
  · refine le_mpMul _ _ _ _ fun l => ?_
    obtain ⟨k, hk⟩ := exists_mpMul_eq B C l j
    calc mpMul (mpMul A B) C i j ≤ mpMul A B i k + C k j := mpMul_le _ _ i j k
      _ ≤ (A i l + B l k) + C k j := by
          have := mpMul_le A B i k l
          linarith
      _ = A i l + (B l k + C k j) := by ring
      _ = A i l + mpMul B C l j := by rw [hk]
  · refine le_mpMul _ _ _ _ fun k => ?_
    obtain ⟨l, hl⟩ := exists_mpMul_eq A B i k
    calc mpMul A (mpMul B C) i j ≤ A i l + mpMul B C l j := mpMul_le _ _ i j l
      _ ≤ A i l + (B l k + C k j) := by
          have := mpMul_le B C l j k
          linarith
      _ = (A i l + B l k) + C k j := by ring
      _ = mpMul A B i k + C k j := by rw [hl]
