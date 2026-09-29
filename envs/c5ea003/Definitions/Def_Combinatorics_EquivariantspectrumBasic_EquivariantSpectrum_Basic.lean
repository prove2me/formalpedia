-- Prove2me | Definitions.Def_Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic
-- name    : Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:41:57.028861+00:00
-- url     : https://prove2.me/theorems/a27fcbc4-89f4-4bbb-911e-3be6fc65a9a1
-- title:
--   Aether Catalog definitions — Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EquivariantspectrumBasic.EquivariantSpectrum.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean by skeleton subtraction
import Mathlib

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

namespace EquivariantSpectrum

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- `T` is `A`-equivariant when it commutes with `A`. -/
def Commutes (A T : V →ₗ[R] V) : Prop := A ∘ₗ T = T ∘ₗ A







/-! ## Conjugation invariance of the spectrum

A group `G` of symmetries acting on an algebra `A` by conjugation, through a
representation `ρ : G →* Aˣ`, leaves the spectrum of every element unchanged.  The
spectrum is therefore a genuine invariant of the `G`-orbit of an operator, and an
operator is *equivariant* precisely when it is a fixed point of this action.
-/

variable {G B : Type*} [Group G] [Ring B] [Algebra R B]

/-- The conjugation action of `G` on `B` through a representation `ρ`. -/
def conjAction (rho : G →* Bˣ) (g : G) (b : B) : B := (rho g : B) * b * (↑(rho g)⁻¹ : B)






end EquivariantSpectrum


