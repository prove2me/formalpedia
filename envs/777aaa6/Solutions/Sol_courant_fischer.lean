-- Prove2me | solution 1 for courant_fischer
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-03T01:06:02.353477+00:00
-- url     : https://prove2.me/submissions/53dd116b-ff41-428a-a100-8cbcbaacd143
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_courant_fischer
import Theorems.Thm_hermitian_kth_eigenvalue_witness
import Theorems.Thm_hermitian_kth_eigenvalue_dual_witness

open Matrix

/-!
# Sketch — `courant_fischer` is the conjunction of the two witness primitives

The `≥` half is exactly `hermitian_kth_eigenvalue_witness`; the `≤` half is
exactly `hermitian_kth_eigenvalue_dual_witness`. Pair them.
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card V)) :
    (∀ W : Submodule ℝ (V → ℝ),
        Fintype.card V - (k : ℕ) ≤ Module.finrank ℝ W →
        ∃ v ∈ W, v ≠ 0 ∧ hA.eigenvalues₀ k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v) ∧
    (∃ W : Submodule ℝ (V → ℝ),
        Module.finrank ℝ W = Fintype.card V - (k : ℕ) ∧
        ∀ u ∈ W, A *ᵥ u ⬝ᵥ u ≤ hA.eigenvalues₀ k * (u ⬝ᵥ u)) :=
  ⟨fun _W hW => hermitian_kth_eigenvalue_witness hA k hW,
   hermitian_kth_eigenvalue_dual_witness hA k⟩
