-- Prove2me | Theorems.Thm_WolfAreaLaw_local_expectations_eq
-- name    : WolfAreaLaw.local_expectations_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:37.448791+00:00
-- url     : https://prove2.me/theorems/52fc73e5-f225-4e6a-9ddc-38461c1decce
-- title:
--   $H_A$, $H_B$ have the same expectation values in $\rho_{AB}$ and $\rho_A\otimes\rho_B$
-- statement:
--   Let $\rho$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ (finite-dimensional) with $\operatorname{tr}\rho=1$, with marginals $\rho_A=\operatorname{tr}_B\rho$ and $\rho_B=\operatorname{tr}_A\rho$. Then for every operator $H_A$ on $\mathcal H_A$ and every operator $H_B$ on $\mathcal H_B$:
--
--   1. $\operatorname{tr}[(H_A\otimes\mathbf 1)(\rho_A\otimes\rho_B)] = \operatorname{tr}[(H_A\otimes\mathbf 1)\,\rho]$;
--   2. $\operatorname{tr}[(\mathbf 1\otimes H_B)(\rho_A\otimes\rho_B)] = \operatorname{tr}[(\mathbf 1\otimes H_B)\,\rho]$.
--
--   In the paper $\rho$ is the thermal state $\rho_{AB}$; this is why the terms $H_A$, $H_B$ cancel when $F(\rho_{AB})\le F(\rho_A\otimes\rho_B)$ is rewritten as Eq. (3), and only the boundary term $H_\partial$ survives.
--
--   Differences from the source:
--   - generalization: the thermal state ρAB and the Hermitian local Hamiltonians HA, HB; equality of the (real) expectation values → every ρ with trace 1, all matrices HA, HB; equality of the complex traces; reason: the thermal state has trace 1, and equal complex traces give equal expectation values; the paper's case is an instance
--   - encoding: HA, HB as operators on the whole system → HA ⊗ₖ 1 and 1 ⊗ₖ HB; reason: physics convention of writing a local operator for its ampliation
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "since HA, HB have the same expectation values in both cases."

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement

open scoped Kronecker

namespace WolfAreaLaw

/-- **Local terms have the same expectation in a state and in the product of its marginals.**
For every operator `ρ` on `H_A ⊗ H_B` with `tr ρ = 1`, with marginals `ρA = Tr_B ρ`,
`ρB = Tr_A ρ`, and all operators `HA` on `H_A` and `HB` on `H_B`:
`tr[(HA ⊗ 1)(ρA ⊗ ρB)] = tr[(HA ⊗ 1) ρ]` and `tr[(1 ⊗ HB)(ρA ⊗ ρB)] = tr[(1 ⊗ HB) ρ]`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "since HA, HB have the same expectation
values in both cases."

**Formalization Note** The paper applies this to the thermal state `ρ = ρAB` and Hermitian
`HA`, `HB`; it holds for every trace-one `ρ` and all `HA`, `HB`. `⊗ₖ` is the Kronecker product,
indexed by `A × B`; `ρA = QAlgorithms.traceRight ρ`, `ρB = QAlgorithms.traceLeft ρ`. -/
theorem local_expectations_eq {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.trace = 1)
    (HA : Matrix A A ℂ) (HB : Matrix B B ℂ) :
    ((HA ⊗ₖ (1 : Matrix B B ℂ)) * (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ)).trace =
        ((HA ⊗ₖ (1 : Matrix B B ℂ)) * ρ).trace ∧
      (((1 : Matrix A A ℂ) ⊗ₖ HB) * (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ)).trace =
        (((1 : Matrix A A ℂ) ⊗ₖ HB) * ρ).trace := by sorry

end WolfAreaLaw
