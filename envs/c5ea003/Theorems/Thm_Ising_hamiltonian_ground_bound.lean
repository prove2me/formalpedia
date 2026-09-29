-- Prove2me | Theorems.Thm_Ising_hamiltonian_ground_bound
-- name    : Ising.hamiltonian_ground_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:24.337793+00:00
-- url     : https://prove2.me/theorems/6fd35331-5661-464d-aebe-556ea0c0649e
-- title:
--   Ground-state lower bound.
-- statement:
--   **Ground-state lower bound.** Every spin configuration has energy at least
--   `-2(m+1)(n+1)`, the value attained by the aligned configurations.
--
--   ```lean
--   theorem Ising.hamiltonian_ground_bound(σ : Config m n) (hσ : IsSpin σ) :
--       -(2 * ((m + 1) * (n + 1) : ℝ)) ≤ hamiltonian σ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/IsingModel/Model.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/IsingModel/Model.lean#L92

-- Thm stub generated from Applications/IsingModel/Model.lean
import Mathlib
import Definitions.Def_Applications_IsingModel_Model

/-!
# The 2D Ising Model on a Periodic Square Lattice

We formalize the ferromagnetic 2D Ising model (units `J = k_B = 1`) on the
torus `Fin (m+1) × Fin (n+1)` (periodic boundary conditions, guaranteeing a
nonempty lattice with cyclic nearest neighbours).  A *spin configuration* assigns
`±1` to each site; the Hamiltonian couples each site to its right and upper
nearest neighbours:
`H(σ) = - Σ_p ( σ_p σ_{p→} + σ_p σ_{p↑} )`.
We prove the ground-state characterisation (all-aligned configurations minimise
energy), the magnetization bounds, and the global `ℤ/2` spin-flip symmetry whose
*spontaneous breaking* below `T_c` is the content of the Peierls argument.

-- !-- Lab Notes -- !--
* **Hypothesis.** The all-up configuration is a ground state with energy `-2N`
  (`N = (m+1)(n+1)`), every configuration has `H ≥ -2N`, and `H` is invariant
  under the global spin flip `σ ↦ -σ` while magnetization is odd.
* **Experiment.** Each bond product `σ_p σ_q ∈ {-1,1}`, so each site contributes
  `≤ 2`; `Finset.sum_le_sum` against the constant `2` gives the bound. The flip
  symmetry is `(-σ_p)(-σ_q) = σ_p σ_q` by `ring`.
* **Analysis.** Survives. The ground-state bound + the *exact* attainment at
  all-up pins the minimum; the flip symmetry with odd magnetization is the
  algebraic skeleton of spontaneous symmetry breaking (a symmetric Hamiltonian
  with a non-symmetric low-temperature state).
* **Critique.** No theorem is trivial: bounds use `rcases` on `±1`, `norm_num`
  on products, and `Finset.sum_le_sum`; the energy of all-up needs a real
  `Finset.sum` evaluation (`Fintype.card_prod`), not `rfl`.
* **Synthesis.** Symmetric `H`, odd `M`, ground states all-up/all-down → the
  Peierls argument (sibling file) shows the symmetry breaks at low `T`.
-/

open Ising

open Finset

variable {m n : ℕ}

theorem Ising.hamiltonian_ground_bound(σ : Config m n) (hσ : IsSpin σ) :
    -(2 * ((m + 1) * (n + 1) : ℝ)) ≤ hamiltonian σ := by sorry
