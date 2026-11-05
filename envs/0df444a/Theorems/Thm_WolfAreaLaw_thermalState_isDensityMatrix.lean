-- Prove2me | Theorems.Thm_WolfAreaLaw_thermalState_isDensityMatrix
-- name    : WolfAreaLaw.thermalState_isDensityMatrix
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:48.372811+00:00
-- url     : https://prove2.me/theorems/6de99b31-b04c-42c6-9edb-d627d01e6c44
-- title:
--   The thermal state $e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ is a density matrix
-- statement:
--   Let $H$ be a Hermitian matrix on a finite-dimensional complex Hilbert space of dimension at least one, and let $\beta\in\mathbb R$. Then the thermal state
--
--   $$
--   \rho_\beta = \frac{e^{-\beta H}}{\operatorname{tr} e^{-\beta H}}
--   $$
--
--   is a density matrix: it is positive semidefinite and has trace $1$.
--
--   The paper uses this silently: it treats the thermal state $\rho_{AB}$ as a state, with marginals $\rho_A,\rho_B$ and a free energy. It is the first step of the proof of Eq. (3).
--
--   Differences from the source:
--   - generalization: the thermal state ρAB of H = HA + H∂ + HB on the composite system A × B, at an inverse temperature β → any finite index type ι, any Hermitian H on it, any real β; reason: the composite system A × B with the paper's H and β > 0 is an instance
--   - encoding: a quantum system (a Hilbert space of dimension at least one) → [Nonempty ι]; reason: excludes only the zero-dimensional space, on which no state exists and which the paper never considers
--   - encoding: the thermal state ρAB at inverse temperature β (named, no formula) → thermalState β H = e^{−βH}/tr e^{−βH} (QAlgorithms.gibbsState (−β • H)); reason: standard definition of the thermal state; the paper's characterization (it minimizes the free energy) is milestone M2
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "The thermal state ρAB corresponding to the inverse temperature β" (used silently)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_WolfAreaLaw_thermalState

namespace WolfAreaLaw

/-- **The thermal state is a state.** For every Hermitian `H` on a nonzero finite-dimensional
space and every real `β`, the thermal state `e^{−βH}/tr e^{−βH}` is a density matrix (positive
semidefinite with trace one).
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2 ("The thermal state ρAB corresponding to
the inverse temperature β"); the page uses this silently when it treats ρAB as a state with
marginals ρA, ρB and a free energy.

**Formalization Note** Stated for an arbitrary finite index type `ι` (the page uses it for the
composite system `A × B`). `[Nonempty ι]` excludes the zero-dimensional space, on which no
density matrix exists. -/
theorem thermalState_isDensityMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) :
    QAlgorithms.IsDensityMatrix (thermalState β H) := by sorry

end WolfAreaLaw
