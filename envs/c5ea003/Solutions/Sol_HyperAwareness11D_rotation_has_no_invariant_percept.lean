-- Prove2me | solution 1 for HyperAwareness11D.rotation_has_no_invariant_percept
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:28:30.642305+00:00
-- url     : https://prove2.me/submissions/a13357fe-f515-42bc-bef1-79afb5a52faf

-- Sol generated from MachineLearning/HyperAwareness11D/SpectralPercept.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_SpectralPercept

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
theorem solution:
    ¬ ∃ (a : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧ linLayer rot2 v = a • v := by
  rintro ⟨a, v, hv, hmv⟩
  have h0 := congrFun hmv 0
  have h1 := congrFun hmv 1
  simp [linLayer, rot2, Fin.sum_univ_succ] at h0 h1
  -- `-v 1 = a * v 0` and `v 0 = a * v 1`, hence `(1 + a²) * v 0 = 0` and likewise for `v 1`
  have hv0 : v 0 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (v 0), sq_nonneg (v 1)]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (v 0), sq_nonneg (v 1)]
  apply hv
  funext i
  fin_cases i
  · simpa using hv0
  · simpa using hv1
