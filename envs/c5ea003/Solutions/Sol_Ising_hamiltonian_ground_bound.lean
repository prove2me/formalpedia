-- Prove2me | solution 1 for Ising.hamiltonian_ground_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:21:48.504129+00:00
-- url     : https://prove2.me/submissions/5d79e70b-4e77-47e4-b7f0-07e325d87a32

-- Sol generated from Applications/IsingModel/Model.lean
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

















open Ising in
theorem solution(σ : Config m n) (hσ : IsSpin σ) :
    -(2 * ((m + 1) * (n + 1) : ℝ)) ≤ hamiltonian σ := by
  have hb : ∀ p : Site m n, σ p * σ (right p) + σ p * σ (up p) ≤ 2 := by
    intro p
    rcases hσ p with h|h <;> rcases hσ (right p) with h2|h2 <;> rcases hσ (up p) with h3|h3 <;>
      rw [h, h2, h3] <;> norm_num
  have hS : ∑ p : Site m n, (σ p * σ (right p) + σ p * σ (up p)) ≤
      2 * ((m + 1) * (n + 1) : ℝ) := by
    calc ∑ p : Site m n, (σ p * σ (right p) + σ p * σ (up p))
        ≤ ∑ _p : Site m n, (2:ℝ) := Finset.sum_le_sum (fun p _ => hb p)
      _ = 2 * ((m + 1) * (n + 1) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring
  unfold hamiltonian; linarith
