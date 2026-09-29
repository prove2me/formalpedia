-- Prove2me | Definitions.Def_Applications_IsingModel_Model
-- name    : Applications_IsingModel_Model
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:08.470448+00:00
-- url     : https://prove2.me/theorems/3b66a206-ab48-4d34-bc2e-ff28134afb4a
-- title:
--   Aether Catalog definitions — Applications_IsingModel_Model
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.IsingModel.Model`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/IsingModel/Model.lean by skeleton subtraction
import Mathlib

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

namespace Ising

open Finset

variable {m n : ℕ}

/-- The lattice (torus) of the Ising model. -/
abbrev Site (m n : ℕ) := Fin (m + 1) × Fin (n + 1)

/-- A configuration is a spin (real) value at each site. -/
abbrev Config (m n : ℕ) := Site m n → ℝ

/-- A configuration is a valid Ising configuration when every spin is `±1`. -/
def IsSpin (σ : Config m n) : Prop := ∀ p, σ p = 1 ∨ σ p = -1

/-- Right nearest neighbour (cyclic in the first coordinate). -/
def right (p : Site m n) : Site m n := (p.1 + 1, p.2)

/-- Upper nearest neighbour (cyclic in the second coordinate). -/
def up (p : Site m n) : Site m n := (p.1, p.2 + 1)

/-- The Ising Hamiltonian with zero external field. -/
noncomputable def hamiltonian (σ : Config m n) : ℝ :=
  - ∑ p : Site m n, (σ p * σ (right p) + σ p * σ (up p))

/-- The total magnetization. -/
noncomputable def magnetization (σ : Config m n) : ℝ := ∑ p : Site m n, σ p

/-- The all-up configuration. -/
def allUp (m n : ℕ) : Config m n := fun _ => 1








end Ising


