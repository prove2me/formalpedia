-- Prove2me | solution 1 for EquivariantSpectrum.ker_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:05.496845+00:00
-- url     : https://prove2.me/submissions/97056993-e81e-4a8f-ab34-5f034d585762

-- Sol generated from Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean
import Mathlib
import Definitions.Def_Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic

/-!
# Equivariant spectrum: basics

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/EquivariantSpectrum/Basic.lean`.  It is reconstructed
here as a self-contained development of the elementary theory of the spectrum of
an operator that is *equivariant* for a group of symmetries.

Setting: `V` a module over a commutative ring `R`, `A : V →ₗ[R] V` an operator,
and `T : V →ₗ[R] V` a symmetry commuting with `A`.  The main results are:

* `EquivariantSpectrum.eigenvector_map` — symmetries permute eigenvectors of a
  given eigenvalue;
* `EquivariantSpectrum.eigenspace_invariant` — eigenspaces are invariant subspaces;
* `EquivariantSpectrum.ker_pow_invariant` — generalized eigenspaces (kernels of
  powers) are invariant;
* `EquivariantSpectrum.spectrum_conj` — the spectrum is a conjugation invariant, so
  it is a genuine invariant of the equivariant isomorphism class.
-/

open EquivariantSpectrum

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]








/-! ## Conjugation invariance of the spectrum

A group `G` of symmetries acting on an algebra `A` by conjugation, through a
representation `ρ : G →* Aˣ`, leaves the spectrum of every element unchanged.  The
spectrum is therefore a genuine invariant of the `G`-orbit of an operator, and an
operator is *equivariant* precisely when it is a fixed point of this action.
-/

variable {G B : Type*} [Group G] [Ring B] [Algebra R B]








open EquivariantSpectrum in
theorem solution(A : V →ₗ[R] V) (m n : ℕ) (hmn : m ≤ n) :
    LinearMap.ker (A ^ m) ≤ LinearMap.ker (A ^ n) := by
  intro v hv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simp only [LinearMap.mem_ker] at hv ⊢
  rw [Nat.add_comm, pow_add, Module.End.mul_apply, hv, map_zero]
