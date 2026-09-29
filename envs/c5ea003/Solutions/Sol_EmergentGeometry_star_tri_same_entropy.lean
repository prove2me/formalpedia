-- Prove2me | solution 1 for EmergentGeometry.star_tri_same_entropy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:05:20.600015+00:00
-- url     : https://prove2.me/submissions/97188461-74e9-42b8-bb99-b1d9cc8cd0c5

-- Sol generated from Novelty/EmergentGeometryNonUniqueness.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_EmergentGeometryNonUniqueness
import Theorems.Thm_EmergentGeometry_entropy_single_bulk

/-!
# The boundary of bulk reconstruction: entropies do not determine the geometry

`Novelty.EREPRBridge` proves that when *every* cell is a boundary cell the
emergent geometry is completely reconstructed from two-point mutual
informations, `w(u,v) = I(u:v)/2`.  This file shows that this reconstruction
theorem is *sharp*: as soon as one hidden bulk cell is allowed, the boundary
entanglement data no longer determines the bulk geometry.

Two explicit three-boundary geometries are compared:

* `starModel`     — a hidden bulk cell joined to each of the three boundary
  cells by a throat of area `1` (a "bulk vertex", the discrete analogue of a
  three-boundary wormhole);
* `triangleModel` — no hidden cell at all, the three boundary cells pairwise
  joined by throats of area `1/2`.

They have *identical* entanglement entropies for every boundary region
(`star_tri_same_entropy`), yet different geometries: in the star the boundary
cells are pairwise non-adjacent (`starModel_no_direct_edge`) while in the
triangle they are.  Consequently the reconstruction map from entanglement to
geometry is not injective in the presence of bulk cells
(`bulk_geometry_not_determined_by_entanglement`), although — by
`bridge_of_mutualInfo_pos` — *connectivity* is still forced: in the star model
the positive mutual information of two boundary cells is carried by a genuine
two-step Einstein–Rosen bridge through the hidden cell
(`starModel_bridge_through_bulk`).
-/

noncomputable section

open EmergentGeometry

open Finset

/-! ## A general one-bulk-cell reduction -/

variable {V : Type*} [Fintype V] [DecidableEq V]


/-! ## The two competing three-boundary geometries -/




lemma threeBdry_three : threeBdry 3 = false := by decide

lemma threeBdry_ne_three : ∀ v : Fin 4, v ≠ 3 → threeBdry v = true := by decide


/-! ## The two geometries are genuinely different -/




/-! ## Entanglement without an edge: a genuine bridge through the bulk -/






open EmergentGeometry in
theorem solution(A : Region (Fin 4)) (hA : A 3 = false) :
    entropy starModel A = entropy triangleModel A := by
  rw [entropy_single_bulk (M := starModel) (c := 3) threeBdry_three threeBdry_ne_three A,
    entropy_single_bulk (M := triangleModel) (c := 3) threeBdry_three threeBdry_ne_three A]
  have hupd : Function.update A (3 : Fin 4) false = A := by
    funext v
    by_cases h : v = 3
    · subst h; simp [hA]
    · simp [Function.update_of_ne h]
  rw [hupd]
  cases h0 : A 0 <;> cases h1 : A 1 <;> cases h2 : A 2 <;>
    simp [cutWeight, Fin.sum_univ_four, sepBit, starModel, triangleModel,
      Function.update_apply, h0, h1, h2, hA] <;> norm_num
