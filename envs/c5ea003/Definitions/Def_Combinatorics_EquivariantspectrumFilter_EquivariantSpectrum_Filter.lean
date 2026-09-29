-- Prove2me | Definitions.Def_Combinatorics_EquivariantspectrumFilter_EquivariantSpectrum_Filter
-- name    : Combinatorics_EquivariantspectrumFilter_EquivariantSpectrum_Filter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:31.188443+00:00
-- url     : https://prove2.me/theorems/68074a8f-476a-47fa-99eb-2e4a0a0302f0
-- title:
--   Aether Catalog definitions — Combinatorics_EquivariantspectrumFilter_EquivariantSpectrum_Filter
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EquivariantspectrumFilter.EquivariantSpectrum.Filter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EquivariantspectrumFilter/EquivariantSpectrum_Filter.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic

/-!
# Equivariant spectrum: the invariant-subspace filtration

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/EquivariantSpectrum/Filter.lean`.  It is reconstructed
here as the lattice/filtration theory attached to the basic equivariant spectrum
module `Shared.EquivariantspectrumBasic.EquivariantSpectrum_Basic`.

Main results:

* `EquivariantSpectrum.Invariant` and the closure of invariant submodules under
  `⊥`, `⊤`, `⊓` and `⊔` (`invariant_inf`, `invariant_sup`, …): the invariant
  subspaces of a symmetry form a sublattice of the submodule lattice;
* `EquivariantSpectrum.kerFiltration` — the ascending filtration by kernels of the
  powers of an operator, shown to be monotone (`kerFiltration_mono`) and
  pointwise invariant under every commuting symmetry (`kerFiltration_invariant`);
* `EquivariantSpectrum.kerFiltration_stabilizes` — once two consecutive steps of
  the filtration agree, the filtration is constant from then on.
-/

namespace EquivariantSpectrum

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A submodule is `T`-invariant if `T` maps it into itself. -/
def Invariant (T : V →ₗ[R] V) (p : Submodule R V) : Prop := ∀ v ∈ p, T v ∈ p







/-! ## The kernel filtration -/

/-- The `n`-th step of the kernel filtration of `A`: the generalized kernel
`ker (Aⁿ)`. -/
def kerFiltration (A : V →ₗ[R] V) (n : ℕ) : Submodule R V := LinearMap.ker (A ^ n)







end EquivariantSpectrum


