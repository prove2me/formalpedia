-- Prove2me | Theorems.Thm_WolfAreaLaw_freeEnergy_le_product_marginals
-- name    : WolfAreaLaw.freeEnergy_le_product_marginals
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:19.291191+00:00
-- url     : https://prove2.me/theorems/3be3bb1e-1d09-47a9-8237-62ad78cb0ee0
-- title:
--   $F(\rho_{AB})\le F(\rho_A\otimes\rho_B)$ for the thermal state
-- statement:
--   Let $\mathcal H_A$, $\mathcal H_B$ be finite-dimensional complex Hilbert spaces, let $H_A$ on $\mathcal H_A$, $H_B$ on $\mathcal H_B$ and $H_\partial$ on $\mathcal H_A\otimes\mathcal H_B$ be Hermitian, and let
--
--   $$
--   H = H_A\otimes\mathbf 1 + \mathbf 1\otimes H_B + H_\partial .
--   $$
--
--   Let $\beta>0$, let $\rho_{AB}=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ be the thermal state, and let $\rho_A=\operatorname{tr}_B\rho_{AB}$ and $\rho_B=\operatorname{tr}_A\rho_{AB}$ be its marginals. Then, with $F(\rho)=\operatorname{tr}[H\rho]-\frac1\beta S(\rho)$,
--
--   $$
--   F(\rho_{AB}) \le F(\rho_A\otimes\rho_B).
--   $$
--
--   This is the instance of the variational principle that the paper turns into the area law (3).
--
--   Differences from the source:
--   - reading: lattice Λ ⊆ Z^D with C^d per site, A a region and B its complement (Λ possibly infinite) → arbitrary finite types A, B (an empty factor is allowed, and both sides are then 0); the composite system is indexed by A × B; reason: the argument compares tr[Hρ], S(ρ) and F(ρ) as finite numbers, and the paper defines none of them on an infinite lattice (p.5 sets aside a direct mutual-information argument when the Hilbert space of B is infinite-dimensional); a finite Λ ⊆ Z^D with a region and its complement is an instance
--   - generalization: sufficiently homogeneous lattice (p.1) with a finite-range Hamiltonian H = HA + H∂ + HB, HA and HB the interaction terms within the regions, H∂ the terms crossing the boundary → arbitrary Hermitian HA on A, HB on B and Hd on A × B, with H = HA ⊗ₖ 1 + 1 ⊗ₖ HB + Hd; reason: the argument uses only this split of H into Hermitian parts; a lattice Hamiltonian with its region / crossing decomposition is an instance
--   - encoding: HA, HB as operators on the whole system → HA ⊗ₖ 1 and 1 ⊗ₖ HB; reason: physics convention of writing a local operator for its ampliation
--   - encoding: log with no base → natural logarithm (WolfAreaLaw.entropy uses Real.log); reason: e^{−βH} and F = tr[Hρ] − S/β fix the natural log; in base 2 the statement is false (classical thermal weights (1−3a, a, a, a) on two qubits with a = 0.001 and HA = HB = 0 give I = 0.00741 bits against a right-hand side of 0.00688)
--   - encoding: tr[·] of a product of Hermitian operators → real part of Matrix.trace; reason: the trace of a product of two Hermitian matrices is real, so taking the real part changes no value
--   - encoding: the thermal state ρAB at inverse temperature β (named, no formula) → thermalState β H = e^{−βH}/tr e^{−βH} (QAlgorithms.gibbsState (−β • H)); reason: standard definition of the thermal state; the paper's characterization (it minimizes the free energy) is milestone M2
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "In particular, F(ρAB) ≤ F(ρA ⊗ ρB)"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_WolfAreaLaw_thermalState
import Definitions.Def_WolfAreaLaw_freeEnergy

open scoped Kronecker

namespace WolfAreaLaw

/-- **`F(ρAB) ≤ F(ρA ⊗ ρB)`.** Let `H = HA ⊗ 1 + 1 ⊗ HB + H∂` on `H_A ⊗ H_B` with `HA`, `HB`, `H∂`
Hermitian, let `β > 0` and let `ρAB = e^{−βH}/tr e^{−βH}` be the thermal state, with marginals
`ρA = Tr_B ρAB`, `ρB = Tr_A ρAB`. Then the free energy of the thermal state is at most the free
energy of the product of its marginals.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "In particular, F(ρAB) ≤ F(ρA ⊗ ρB)".

**Formalization Note** The composite system is indexed by `A × B` and `⊗ₖ` is the Kronecker
product. The paper writes `HA`, `HB` for `HA ⊗ 1`, `1 ⊗ HB`. `ρA = QAlgorithms.traceRight ρ`
(traces out `B`), `ρB = QAlgorithms.traceLeft ρ` (traces out `A`). The lattice structure of the
paper (finite-range interactions, `A` a region, `B` its complement) is not used: `A`, `B` are
arbitrary finite types and `HA`, `HB`, `H∂` arbitrary Hermitian matrices. -/
theorem freeEnergy_le_product_marginals {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (HA : Matrix A A ℂ) (HB : Matrix B B ℂ) (Hd : Matrix (A × B) (A × B) ℂ)
    (hHA : HA.IsHermitian) (hHB : HB.IsHermitian) (hHd : Hd.IsHermitian) (β : ℝ) (hβ : 0 < β) :
    let H := HA ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ HB + Hd
    let ρ := thermalState β H
    freeEnergy β H ρ ≤ freeEnergy β H (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) := by sorry

end WolfAreaLaw
