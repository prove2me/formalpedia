-- Prove2me | Theorems.Thm_WolfAreaLaw_entropy_kronecker
-- name    : WolfAreaLaw.entropy_kronecker
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:18.78024+00:00
-- url     : https://prove2.me/theorems/87f77c2d-0ea6-4d10-bd75-f7b7c0ab2d14
-- title:
--   $S(\rho_A\otimes\rho_B)=S(\rho_A)+S(\rho_B)$ for density matrices
-- statement:
--   Let $\rho_A$ and $\rho_B$ be density matrices on finite-dimensional complex Hilbert spaces $\mathcal H_A$ and $\mathcal H_B$. Then the von Neumann entropy is additive on their tensor product:
--
--   $$
--   S(\rho_A\otimes\rho_B) = S(\rho_A) + S(\rho_B).
--   $$
--
--   The paper uses this identity silently in passing from $F(\rho_{AB})\le F(\rho_A\otimes\rho_B)$ to Eq. (3): it turns the entropy term of $F(\rho_A\otimes\rho_B)$ into $S(\rho_A)+S(\rho_B)$, which together with $-S(\rho_{AB})$ gives the mutual information.
--
--   **Formalization Note** The trace-one hypotheses are needed: for general positive semidefinite $X,Y$ one has $S(X\otimes Y)=\operatorname{tr}Y\cdot S(X)+\operatorname{tr}X\cdot S(Y)$.
--
--   Differences from the source:
--   - generalization: the marginals ρA, ρB of the thermal state → arbitrary density matrices ρA on A and ρB on B; reason: the marginals of a state are density matrices, so the paper's case is an instance
--   - encoding: log with no base → natural logarithm (WolfAreaLaw.entropy uses Real.log); reason: the paper's entropy is in nats, since e^{−βH} and F = tr[Hρ] − S/β fix the base; additivity itself holds in every base
--   - encoding: ρA ⊗ ρB → Kronecker product ρA ⊗ₖ ρB indexed by A × B; reason: the matrix of the tensor product in the product basis
--   - encoding: S(ρ) = −tr[ρ log ρ] → minus the real part of the trace of cfc (x log x) applied to ρ (WolfAreaLaw.entropy); reason: on a density matrix ρ log ρ is f(ρ) for f(x) = x log x with 0 log 0 = 0, and its trace is real
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "In particular, F(ρAB) ≤ F(ρA ⊗ ρB) from which we obtain" (used silently)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_WolfAreaLaw_entropy

open scoped Kronecker

namespace WolfAreaLaw

/-- **Additivity of the von Neumann entropy on product states.** For density matrices `ρA` on
`H_A` and `ρB` on `H_B`, `S(ρA ⊗ ρB) = S(ρA) + S(ρB)`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "In particular, F(ρAB) ≤ F(ρA ⊗ ρB) from
which we obtain" (3). The page uses this identity silently: it turns the free energy of the
product state into `tr[H(ρA ⊗ ρB)] − (S(ρA) + S(ρB))/β`.

**Formalization Note** `⊗ₖ` is the Kronecker product, indexed by `A × B`; `S` is the
natural-log `WolfAreaLaw.entropy`. The trace-one hypotheses are needed: for general positive
semidefinite `X`, `Y` the identity reads `S(X ⊗ Y) = tr Y · S(X) + tr X · S(Y)`. -/
theorem entropy_kronecker {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρA : Matrix A A ℂ) (ρB : Matrix B B ℂ) (hA : QAlgorithms.IsDensityMatrix ρA)
    (hB : QAlgorithms.IsDensityMatrix ρB) :
    entropy (ρA ⊗ₖ ρB) = entropy ρA + entropy ρB := by sorry

end WolfAreaLaw
