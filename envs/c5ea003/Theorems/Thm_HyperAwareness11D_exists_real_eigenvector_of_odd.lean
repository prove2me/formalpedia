-- Prove2me | Theorems.Thm_HyperAwareness11D_exists_real_eigenvector_of_odd
-- name    : HyperAwareness11D.exists_real_eigenvector_of_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:02.517152+00:00
-- url     : https://prove2.me/theorems/35cb0bc8-cc89-445e-adfb-9d508f59b980
-- title:
--   Every real square matrix of odd size has a real eigenvalue.
-- statement:
--   **Every real square matrix of odd size has a real eigenvalue.**
--
--   ```lean
--   theorem HyperAwareness11D.exists_real_eigenvector_of_odd{m : ℕ} (hm : Odd m) (M : Matrix (Fin m) (Fin m) ℝ) :
--       ∃ (a : ℝ) (v : Fin m → ℝ), v ≠ 0 ∧ M.mulVec v = a • v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/SpectralPercept.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/SpectralPercept.lean#L72

-- Thm stub generated from MachineLearning/HyperAwareness11D/SpectralPercept.lean
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

theorem HyperAwareness11D.exists_real_eigenvector_of_odd{m : ℕ} (hm : Odd m) (M : Matrix (Fin m) (Fin m) ℝ) :
    ∃ (a : ℝ) (v : Fin m → ℝ), v ≠ 0 ∧ M.mulVec v = a • v := by sorry
