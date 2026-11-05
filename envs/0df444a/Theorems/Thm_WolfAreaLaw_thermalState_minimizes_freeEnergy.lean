-- Prove2me | Theorems.Thm_WolfAreaLaw_thermalState_minimizes_freeEnergy
-- name    : WolfAreaLaw.thermalState_minimizes_freeEnergy
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:14.657194+00:00
-- url     : https://prove2.me/theorems/896273f5-5812-48c8-896e-9482801ae77c
-- title:
--   Gibbs variational principle: the thermal state minimizes the free energy
-- statement:
--   Let $H$ be a Hermitian matrix on a finite-dimensional complex Hilbert space of dimension at least one, let $\beta>0$, and let $\rho_\beta=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ be the thermal state. For every density matrix $\sigma$ on the same space,
--
--   $$
--   F(\rho_\beta) \le F(\sigma), \qquad F(\rho) = \operatorname{tr}[H\rho] - \frac1\beta S(\rho),
--   $$
--
--   where $S(\rho)=-\operatorname{tr}[\rho\log\rho]$ is the von Neumann entropy. That is, the thermal state minimizes the free energy over all states.
--
--   This is the variational principle on which the paper's area law rests: comparing the thermal state with the product of its own marginals gives Eq. (3).
--
--   Differences from the source:
--   - generalization: the thermal state ρAB of H = HA + H∂ + HB on the composite system A × B → any finite index type ι and any Hermitian H on it; reason: the composite system A × B with the paper's H is an instance
--   - encoding: a quantum system (a Hilbert space of dimension at least one) → [Nonempty ι]; reason: excludes only the zero-dimensional space, on which no state exists and which the paper never considers
--   - encoding: log with no base → natural logarithm (WolfAreaLaw.entropy uses Real.log); reason: e^{−βH} and F = tr[Hρ] − S/β fix the natural log; it is the only base in which the statement holds as printed
--   - encoding: tr[·] of a product of Hermitian operators → real part of Matrix.trace; reason: the trace of a product of two Hermitian matrices is real, so taking the real part changes no value
--   - encoding: the thermal state ρAB at inverse temperature β (named, no formula) → thermalState β H = e^{−βH}/tr e^{−βH} (QAlgorithms.gibbsState (−β • H)); reason: standard definition of the thermal state; the paper's characterization (it minimizes the free energy) is what this item proves of that formula
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "The thermal state ρAB corresponding to the inverse temperature β minimizes the free energy F(ρ) = tr[Hρ] − (1/β) S(ρ)."

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_WolfAreaLaw_thermalState
import Definitions.Def_WolfAreaLaw_freeEnergy

namespace WolfAreaLaw

/-- **Gibbs variational principle.** For a Hermitian `H` on a nonzero finite-dimensional space and
`β > 0`, the thermal state `ρ_β = e^{−βH}/tr e^{−βH}` minimizes the free energy
`F(ρ) = tr[Hρ] − (1/β) S(ρ)` over all density matrices: `F(ρ_β) ≤ F(σ)` for every state `σ`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "The thermal state ρAB corresponding to
the inverse temperature β minimizes the free energy F(ρ) = tr[Hρ] − (1/β) S(ρ)."

**Formalization Note** Stated for an arbitrary finite index type `ι` (the page uses it for the
composite system `A × B` with `H = HA + H∂ + HB`). `S` is the natural-log
`WolfAreaLaw.entropy`; states are `QAlgorithms.IsDensityMatrix` (PSD, trace one). `[Nonempty ι]`
excludes the zero-dimensional space, on which no state exists. -/
theorem thermalState_minimizes_freeEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (β : ℝ) (hβ : 0 < β)
    (σ : Matrix ι ι ℂ) (hσ : QAlgorithms.IsDensityMatrix σ) :
    freeEnergy β H (thermalState β H) ≤ freeEnergy β H σ := by sorry

end WolfAreaLaw
