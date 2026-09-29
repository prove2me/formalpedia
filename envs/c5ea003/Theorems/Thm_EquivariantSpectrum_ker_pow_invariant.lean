-- Prove2me | Theorems.Thm_EquivariantSpectrum_ker_pow_invariant
-- name    : EquivariantSpectrum.ker_pow_invariant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:17:20.494866+00:00
-- url     : https://prove2.me/theorems/38953701-768f-4b91-a340-ce9e8f45e33a
-- title:
--   Generalized eigenspaces are invariant.
-- statement:
--   **Generalized eigenspaces are invariant.**  Kernels of powers of `A` are stable
--   under any symmetry commuting with `A`.
--
--   ```lean
--   theorem EquivariantSpectrum.ker_pow_invariant{A T : V →ₗ[R] V} (h : Commutes A T) (n : ℕ) :
--       ∀ v ∈ LinearMap.ker (A ^ n), T v ∈ LinearMap.ker (A ^ n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EquivariantspectrumBasic/EquivariantSpectrum_Basic.lean#L57

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

theorem EquivariantSpectrum.ker_pow_invariant{A T : V →ₗ[R] V} (h : Commutes A T) (n : ℕ) :
    ∀ v ∈ LinearMap.ker (A ^ n), T v ∈ LinearMap.ker (A ^ n) := by sorry
