-- Prove2me | Theorems.Thm_EquivariantSpectrum_kerFiltration_stabilizes
-- name    : EquivariantSpectrum.kerFiltration_stabilizes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:17:25.018563+00:00
-- url     : https://prove2.me/theorems/f13c61bc-30af-404c-a8e8-c22fb55ce9e4
-- title:
--   Stabilization.
-- statement:
--   **Stabilization.**  If two consecutive steps of the kernel filtration agree, the
--   filtration is constant from that point on.
--
--   ```lean
--   theorem EquivariantSpectrum.kerFiltration_stabilizes(A : V →ₗ[R] V) (n : ℕ)
--       (h : kerFiltration A (n + 1) = kerFiltration A n) :
--       ∀ m, n ≤ m → kerFiltration A m = kerFiltration A n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EquivariantspectrumFilter/EquivariantSpectrum_Filter.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EquivariantspectrumFilter/EquivariantSpectrum_Filter.lean#L93

-- Thm stub generated from Combinatorics/EquivariantspectrumFilter/EquivariantSpectrum_Filter.lean
import Mathlib
import Definitions.Def_Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic
import Definitions.Def_Combinatorics_EquivariantspectrumFilter_EquivariantSpectrum_Filter

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

open EquivariantSpectrum

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]








/-! ## The kernel filtration -/

theorem EquivariantSpectrum.kerFiltration_stabilizes(A : V →ₗ[R] V) (n : ℕ)
    (h : kerFiltration A (n + 1) = kerFiltration A n) :
    ∀ m, n ≤ m → kerFiltration A m = kerFiltration A n := by sorry
