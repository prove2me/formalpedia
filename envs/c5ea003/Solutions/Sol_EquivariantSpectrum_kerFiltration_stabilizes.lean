-- Prove2me | solution 1 for EquivariantSpectrum.kerFiltration_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:33:09.610045+00:00
-- url     : https://prove2.me/submissions/e380e6ac-4834-41b5-974c-84de51d9bb02

-- Sol generated from Combinatorics/EquivariantspectrumFilter/EquivariantSpectrum_Filter.lean
import Mathlib
import Definitions.Def_Combinatorics_EquivariantspectrumBasic_EquivariantSpectrum_Basic
import Definitions.Def_Combinatorics_EquivariantspectrumFilter_EquivariantSpectrum_Filter
import Theorems.Thm_EquivariantSpectrum_ker_pow_mono

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



lemma mem_kerFiltration {A : V →ₗ[R] V} {n : ℕ} {v : V} :
    v ∈ kerFiltration A n ↔ (A ^ n) v = 0 := Iff.rfl

/-- The kernel filtration is ascending. -/
theorem kerFiltration_mono (A : V →ₗ[R] V) : Monotone (kerFiltration A) :=
  fun _ _ hmn => ker_pow_mono A _ _ hmn





open EquivariantSpectrum in
theorem solution(A : V →ₗ[R] V) (n : ℕ)
    (h : kerFiltration A (n + 1) = kerFiltration A n) :
    ∀ m, n ≤ m → kerFiltration A m = kerFiltration A n := by
  have step : ∀ k, kerFiltration A (n + k) = kerFiltration A n := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih =>
        refine le_antisymm ?_ (kerFiltration_mono A (by omega))
        intro v hv
        -- `A v` lies in `ker (A ^ (n + j))`, hence in `ker (A ^ n)` by induction
        have hAv : A v ∈ kerFiltration A (n + j) := by
          rw [mem_kerFiltration] at hv ⊢
          rw [show n + (j + 1) = (n + j) + 1 by omega, pow_succ] at hv
          rwa [Module.End.mul_apply] at hv
        rw [ih] at hAv
        have : v ∈ kerFiltration A (n + 1) := by
          rw [mem_kerFiltration] at hAv ⊢
          rw [pow_succ, Module.End.mul_apply]
          exact hAv
        rwa [h] at this
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact step k
