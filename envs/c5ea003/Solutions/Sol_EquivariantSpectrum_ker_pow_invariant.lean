-- Prove2me | solution 1 for EquivariantSpectrum.ker_pow_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:18:01.087317+00:00
-- url     : https://prove2.me/submissions/cf3cf36e-8095-4845-8b00-d68819bdde43

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


lemma Commutes.apply {A T : V →ₗ[R] V} (h : Commutes A T) (v : V) : A (T v) = T (A v) :=
  congrArg (fun L : V →ₗ[R] V => L v) h



/-- If `T` commutes with `A` then it commutes with every power of `A`. -/
theorem commutes_pow {A T : V →ₗ[R] V} (h : Commutes A T) (n : ℕ) :
    Commutes (A ^ n) T := by
  induction n with
  | zero => ext v; simp
  | succ k ih =>
      ext v
      simp only [pow_succ, LinearMap.comp_apply, Module.End.mul_apply]
      rw [Commutes.apply h v]
      exact Commutes.apply ih (A v)



/-! ## Conjugation invariance of the spectrum

A group `G` of symmetries acting on an algebra `A` by conjugation, through a
representation `ρ : G →* Aˣ`, leaves the spectrum of every element unchanged.  The
spectrum is therefore a genuine invariant of the `G`-orbit of an operator, and an
operator is *equivariant* precisely when it is a fixed point of this action.
-/

variable {G B : Type*} [Group G] [Ring B] [Algebra R B]








open EquivariantSpectrum in
theorem solution{A T : V →ₗ[R] V} (h : Commutes A T) (n : ℕ) :
    ∀ v ∈ LinearMap.ker (A ^ n), T v ∈ LinearMap.ker (A ^ n) := by
  intro v hv
  simp only [LinearMap.mem_ker] at hv ⊢
  rw [Commutes.apply (commutes_pow h n) v, hv, map_zero]
