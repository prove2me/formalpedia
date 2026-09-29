-- Prove2me | solution 1 for QuantumWalkCayley.cycle_second_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:08.114443+00:00
-- url     : https://prove2.me/submissions/c041d767-18e8-418f-a4e0-66431683f1af

-- Sol generated from Bridges/QuantumWalkCayley.lean
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






open QuantumWalkCayley in
theorem solution(n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    charEigenvalue (cycleGen n) (ZMod.stdAddChar) =
      (2 * Real.cos (2 * Real.pi / n) : ℂ) := by
  have h1 : (1 : ZMod n) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod n) = 0 := by linear_combination h
    have h3 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; exact h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3; omega
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hval : (1 : ZMod n).val = 1 := ZMod.val_one n
  have hz : ZMod.stdAddChar (1 : ZMod n) =
      Complex.exp (((2 * Real.pi / n) : ℝ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hval]; push_cast; ring_nf
  unfold charEigenvalue cycleGen
  rw [Finset.sum_pair h1, AddChar.map_neg_eq_inv]
  have hnorm : ‖ZMod.stdAddChar (1 : ZMod n)‖ = 1 := AddChar.norm_apply _ _
  rw [Complex.inv_eq_conj hnorm, Complex.add_conj, hz, Complex.exp_ofReal_mul_I_re]
  push_cast; ring
