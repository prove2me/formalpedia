-- Prove2me | Theorems.Thm_QuantumWalkCayley_cycle_second_eigenvalue
-- name    : QuantumWalkCayley.cycle_second_eigenvalue
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:08:58.32528+00:00
-- url     : https://prove2.me/theorems/f766b7cb-2bc1-4b4f-a625-e453c5c844e0
-- title:
--   For `n ≥ 3`, the standard character's eigenvalue on the cycle is `2 cos(2π/n)` — the
-- statement:
--   For `n ≥ 3`, the standard character's eigenvalue on the cycle is `2 cos(2π/n)` — the
--   classical "second eigenvalue" of the cycle graph.
--
--   ```lean
--   theorem QuantumWalkCayley.cycle_second_eigenvalue(n : ℕ) [NeZero n] (hn : 3 ≤ n) :
--       charEigenvalue (cycleGen n) (ZMod.stdAddChar) =
--         (2 * Real.cos (2 * Real.pi / n) : ℂ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantumWalkCayley.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantumWalkCayley.lean#L176

-- Thm stub generated from Bridges/QuantumWalkCayley.lean
import Mathlib
import Definitions.Def_Bridges_QuantumWalkCayley

/-!
# Quantum Random Walks on Cayley Graphs: Spectral Theory of Abelian Cayley Graphs

This file develops the spectral theory underlying (classical and quantum) random walks
on Cayley graphs of **finite abelian groups**.  The key phenomenon powering every
statement about spectral gaps and mixing times is that the *characters* of an abelian
group simultaneously diagonalize every translation-invariant operator — in particular
the adjacency/walk operator of any Cayley graph.

We model the Hilbert space `ℓ²(G)` as functions `G → ℂ`.

## Main definitions

* `QuantumWalkCayley.shift s` — the elementary translation ("coin-free quantum walk step")
  `f ↦ (x ↦ f (x + s))`.  This is the unitary generator associated to a single group
  element `s`.
* `QuantumWalkCayley.adjacency S` — the Cayley-graph adjacency (walk) operator
  `f ↦ (x ↦ ∑_{s ∈ S} f (x + s))` for a generating (multi)set `S`.
* `QuantumWalkCayley.ell2normSq f = ∑_x ‖f x‖²` — the squared `ℓ²` norm.
* `QuantumWalkCayley.charEigenvalue S ψ = ∑_{s ∈ S} ψ s` — the eigenvalue attached to a
  character `ψ`.

## Main results

* `shift_preserves_ell2normSq` — each shift is an isometry of `ℓ²(G)` (unitarity).
* `shift_iterate` / `shift_periodic` — the single-generator quantum walk is **periodic**
  with period dividing the additive order of `s`.
* `adjacency_addChar_eigen` — **every additive character is an eigenvector** of the walk
  operator, with eigenvalue `charEigenvalue S ψ`.  This is the spectral diagonalization
  at the heart of the theory.
* `charEigenvalue_trivial` — the trivial character yields the top ("degree") eigenvalue.
* `charEigenvalue_norm_le` — every eigenvalue has modulus `≤ |S|` (Perron/Frobenius bound).
* `charEigenvalue_real_of_symmetric` — for a **symmetric** generating set the eigenvalues
  are real (so the walk operator is self-adjoint).
* `cycle_second_eigenvalue` — for the cycle `Cay(ℤ/nℤ, {±1})` the standard character has
  eigenvalue `2 cos(2π/n)`, and `cycle_spectral_gap_pos` shows the spectral gap is strictly
  positive.
-/

open scoped BigOperators

open QuantumWalkCayley

variable {G : Type*} [AddCommGroup G]





/-! ### Algebraic structure of the shift operator -/








/-! ### Periodicity of the single-generator quantum walk -/



/-! ### Translation invariance of the walk operator -/


/-! ### Spectral diagonalization by characters -/






/-! ### The cycle graph `Cay(ℤ/nℤ, {±1})` -/

theorem QuantumWalkCayley.cycle_second_eigenvalue(n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    charEigenvalue (cycleGen n) (ZMod.stdAddChar) =
      (2 * Real.cos (2 * Real.pi / n) : ℂ) := by sorry
