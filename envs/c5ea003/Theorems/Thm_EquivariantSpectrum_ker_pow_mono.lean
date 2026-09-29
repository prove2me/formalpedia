-- Prove2me | Theorems.Thm_EquivariantSpectrum_ker_pow_mono
-- name    : EquivariantSpectrum.ker_pow_mono
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:17:13.268985+00:00
-- url     : https://prove2.me/theorems/815ae90a-52c2-4433-9aef-1fd984f50699
-- title:
--   The kernels of the powers of `A` form an ascending filtration.
-- statement:
--   The kernels of the powers of `A` form an ascending filtration.
--
--   ```lean
--   theorem EquivariantSpectrum.ker_pow_mono(A : V →ₗ[R] V) (m n : ℕ) (hmn : m ≤ n) :
--       LinearMap.ker (A ^ m) ≤ LinearMap.ker (A ^ n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean#L65

-- Thm stub generated from Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean
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

theorem EquivariantSpectrum.ker_pow_mono(A : V →ₗ[R] V) (m n : ℕ) (hmn : m ≤ n) :
    LinearMap.ker (A ^ m) ≤ LinearMap.ker (A ^ n) := by sorry
