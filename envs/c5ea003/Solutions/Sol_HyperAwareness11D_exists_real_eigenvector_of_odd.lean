-- Prove2me | solution 1 for HyperAwareness11D.exists_real_eigenvector_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:19:43.9665+00:00
-- url     : https://prove2.me/submissions/1efb1e43-e045-47cc-9167-b6a21ba7739b

-- Sol generated from MachineLearning/HyperAwareness11D/SpectralPercept.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_SpectralPercept
import Theorems.Thm_HyperAwareness11D_exists_real_root_of_odd_natDegree

/-!
# Hyper-Awareness V: the parity dividend — every 11-dimensional layer has an invariant percept

Dimension `11` is *odd*, and this file extracts the structural dividend that odd parity pays
to an 11-dimensional perception architecture:

> **Every** linear perception layer on `ℝ¹¹` — with no assumption whatsoever on its weights —
> possesses a nonzero percept direction that it merely rescales.

Equivalently, every `11 × 11` real weight matrix has a real eigenvalue.  This is a genuinely
cross-domain statement: the algebra of the characteristic polynomial meets the topology of
the real line (the intermediate value theorem), and the conclusion fails in even dimensions.

## Main results

* `HyperAwareness11D.exists_real_root_of_odd_natDegree` — a monic real polynomial of odd
  degree has a real root (proved from the asymptotics of polynomials plus the intermediate
  value theorem; Mathlib has no `IsRealClosed ℝ` instance).
* `HyperAwareness11D.exists_real_eigenvector_of_odd` — every real square matrix of odd size
  has a real eigenvalue with a nonzero eigenvector.
* `HyperAwareness11D.exists_invariant_percept_11` — the 11-dimensional statement for
  `linLayer`.
* `HyperAwareness11D.rotation_has_no_invariant_percept` — the *boundary*: in dimension `2`
  the quarter-turn layer has no invariant percept direction, so the result above is a genuine
  consequence of the oddness of `11` and not a formal triviality.
-/

open HyperAwareness11D

open Polynomial Filter Topology

noncomputable section

/-! ## A monic real polynomial of odd degree has a root -/


/-! ## Real eigenvalues in odd dimension -/





/-! ## The boundary: parity is essential -/





open HyperAwareness11D in
theorem solution{m : ℕ} (hm : Odd m) (M : Matrix (Fin m) (Fin m) ℝ) :
    ∃ (a : ℝ) (v : Fin m → ℝ), v ≠ 0 ∧ M.mulVec v = a • v := by
  have hmonic : M.charpoly.Monic := M.charpoly_monic
  have hdeg : M.charpoly.natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨t, ht⟩ := exists_real_root_of_odd_natDegree hmonic (by rw [hdeg]; exact hm)
  have hdet : (Matrix.scalar (Fin m) t - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact ht
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨t, v, hv, ?_⟩
  rw [Matrix.sub_mulVec] at hmv
  have hs : (Matrix.scalar (Fin m) t).mulVec v = t • v := by
    funext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  rw [hs] at hmv
  funext i
  have hi := congrFun hmv i
  simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hi
  show M.mulVec v i = t * v i
  linarith
