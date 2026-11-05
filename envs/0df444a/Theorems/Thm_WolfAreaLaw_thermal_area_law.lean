-- Prove2me | Theorems.Thm_WolfAreaLaw_thermal_area_law
-- name    : WolfAreaLaw.thermal_area_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:52:03.547666+00:00
-- url     : https://prove2.me/theorems/beeea9d7-4f13-4fe4-b607-efc981663f74
-- title:
--   Eq. (3): $I(A:B)\le\beta\operatorname{tr}[H_\partial(\rho_A\otimes\rho_B-\rho_{AB})]$ for thermal states
-- statement:
--   This is the finite-temperature area law for the mutual information.
--
--   Let $\mathcal H_A$, $\mathcal H_B$ be finite-dimensional complex Hilbert spaces (in the paper: a region $A$ of a lattice and its complement $B$). Let $H_A$ on $\mathcal H_A$, $H_B$ on $\mathcal H_B$ and $H_\partial$ on $\mathcal H_A\otimes\mathcal H_B$ be Hermitian, and let
--
--   $$
--   H = H_A\otimes\mathbf 1 + \mathbf 1\otimes H_B + H_\partial
--   $$
--
--   ($H_A$, $H_B$ collect the interactions inside the two regions and $H_\partial$ those crossing the boundary). Let $\beta>0$, let $\rho_{AB}=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ be the thermal state at inverse temperature $\beta$, and let $\rho_A=\operatorname{tr}_B\rho_{AB}$, $\rho_B=\operatorname{tr}_A\rho_{AB}$ be its marginals. Then
--
--   $$
--   I(A:B) \le \beta\,\operatorname{tr}\big[H_\partial(\rho_A\otimes\rho_B-\rho_{AB})\big],
--   $$
--
--   where $I(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$ and $S(\rho)=-\operatorname{tr}[\rho\log\rho]$ is the von Neumann entropy.
--
--   The right-hand side depends only on the boundary term $H_\partial$, so for a finite-range lattice Hamiltonian the mutual information between a region and its complement grows at most like the boundary of the region, at every finite temperature.
--
--   Differences from the source:
--   - reading: lattice Λ ⊆ Z^D with C^d per site, A a region and B its complement (Λ possibly infinite) → arbitrary finite types A, B (an empty factor is allowed, and both sides are then 0); the composite system is indexed by A × B; reason: the argument compares tr[Hρ], S(ρ) and F(ρ) as finite numbers, and the paper defines none of them on an infinite lattice (p.5 sets aside a direct mutual-information argument when the Hilbert space of B is infinite-dimensional); a finite Λ ⊆ Z^D with a region and its complement is an instance
--   - generalization: sufficiently homogeneous lattice (p.1) with a finite-range Hamiltonian H = HA + H∂ + HB, HA and HB the interaction terms within the regions, H∂ the terms crossing the boundary → arbitrary Hermitian HA on A, HB on B and Hd on A × B, with H = HA ⊗ₖ 1 + 1 ⊗ₖ HB + Hd; reason: the argument uses only this split of H into Hermitian parts; a lattice Hamiltonian with its region / crossing decomposition is an instance
--   - encoding: log with no base → natural logarithm (WolfAreaLaw.entropy uses Real.log); reason: e^{−βH} and F = tr[Hρ] − S/β fix the natural log; in base 2 the statement is false (classical thermal weights (1−3a, a, a, a) on two qubits with a = 0.001 and HA = HB = 0 give I = 0.00741 bits against a right-hand side of 0.00688)
--   - encoding: HA, HB as operators on the whole system → HA ⊗ₖ 1 and 1 ⊗ₖ HB; reason: physics convention of writing a local operator for its ampliation
--   - encoding: tr[·] of a product of Hermitian operators → real part of Matrix.trace; reason: the trace of a product of two Hermitian matrices is real, so taking the real part changes no value
--   - encoding: the thermal state ρAB at inverse temperature β (named, no formula) → thermalState β H = e^{−βH}/tr e^{−βH} (QAlgorithms.gibbsState (−β • H)); reason: standard definition of the thermal state; the paper's characterization (it minimizes the free energy) is milestone M2
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, Eq. (3), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_WolfAreaLaw_thermalState
import Definitions.Def_WolfAreaLaw_mutualInfo

open scoped Kronecker

namespace WolfAreaLaw

/-- **Finite-temperature area law for the mutual information (Eq. (3)).** Let
`H = HA ⊗ 1 + 1 ⊗ HB + H∂` on `H_A ⊗ H_B` with `HA`, `HB`, `H∂` Hermitian, let `β > 0`, and let
`ρAB = e^{−βH}/tr e^{−βH}` be the thermal state with marginals `ρA = Tr_B ρAB`,
`ρB = Tr_A ρAB`. Then
`I(A : B) ≤ β tr[H∂(ρA ⊗ ρB − ρAB)]`.
Wolf–Verstraete–Hastings–Cirac, *Area laws in quantum systems: mutual information and
correlations*, arXiv:0704.3906v2, Eq. (3), p.2.

**Formalization Note** The paper's lattice `Λ ⊆ Z^D`, region `A` with complement `B`, and
finite-range Hamiltonian are replaced by arbitrary finite systems `A`, `B` and arbitrary Hermitian
`HA`, `HB`, `H∂` (the argument uses only the split `H = HA + H∂ + HB`; a finite lattice region and
its complement are an instance). The paper writes `HA`, `HB` for `HA ⊗ 1`, `1 ⊗ HB`. The composite
system is indexed by `A × B` and `⊗ₖ` is the Kronecker product. `ρA = QAlgorithms.traceRight ρ`
(traces out `B`), `ρB = QAlgorithms.traceLeft ρ` (traces out `A`). Entropies use the natural
logarithm (`WolfAreaLaw.entropy`), the base fixed by `e^{−βH}`. `tr[·]` is the real part of the
trace, which is real here. -/
theorem thermal_area_law {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (HA : Matrix A A ℂ) (HB : Matrix B B ℂ) (Hd : Matrix (A × B) (A × B) ℂ)
    (hHA : HA.IsHermitian) (hHB : HB.IsHermitian) (hHd : Hd.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    let ρ := thermalState β (HA ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ HB + Hd)
    mutualInfo ρ ≤
      β * (Hd * (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ - ρ)).trace.re := by sorry

end WolfAreaLaw
