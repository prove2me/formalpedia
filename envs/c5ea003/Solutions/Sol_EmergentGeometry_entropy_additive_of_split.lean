-- Prove2me | solution 1 for EmergentGeometry.entropy_additive_of_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:54:55.455135+00:00
-- url     : https://prove2.me/submissions/053cd048-60ec-4e19-ab21-b5866a0b5f1c

-- Sol generated from Novelty/EREPRBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_cutWeight_comb
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_entropy_subadditive
import Theorems.Thm_EmergentGeometry_exists_minimal_surface
import Theorems.Thm_EmergentGeometry_sepBit_self

/-!
# ER = EPR: bulk bridges are exactly boundary entanglement

Building on `Novelty.EmergentGeometryEntropyCone` (min-cut / Ryu–Takayanagi
entropies of a finite bulk geometry) and on `Novelty.EREqualsEPR` (the two-qubit
toy model), this file proves the two halves of the ER=EPR correspondence in the
toy setting:

* **Geometry from entanglement** (`weight_eq_half_mutualInfo`,
  `bulk_weights_determined_by_mutualInfo`): in a model without hidden bulk cells
  every edge weight — i.e. the entire bulk metric — is recovered from
  two-point mutual informations, `w(u,v) = I(u:v)/2`.
* **Entanglement forces a bridge** (`mutualInfo_eq_zero_of_no_bridge`,
  `bridge_of_mutualInfo_pos`): two boundary regions with positive mutual
  information *must* be joined by a positive-weight bulk path, an
  Einstein–Rosen bridge; conversely disconnected regions are unentangled
  (their entropies are exactly additive).
* **EPR ⟺ ER for a qubit pair** (`ER_EPR_correspondence`): a real two-qubit
  pure state is entangled if and only if the associated one-throat geometry,
  whose throat weight is the concurrence, contains a bulk bridge between the
  two boundary qubits.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Boundary regions consisting of one or two cells -/









/-! ## Bulk connectivity: Einstein–Rosen bridges -/






/-! ## The single-throat geometry of a qubit pair -/





/-! ## Two-qubit states: entanglement is a bridge -/

open EmergentSpacetime







open EmergentGeometry in
theorem solution{M : HoloModel V} {U : Region V}
    (hU : ∀ x y, U x = true → U y = false → M.weight x y = 0)
    (A B : Region V) (hA : ∀ v, A v = true → U v = true)
    (hB : ∀ v, B v = true → U v = false) :
    entropy M (fun v => A v || B v) = entropy M A + entropy M B := by
  refine le_antisymm (entropy_subadditive M A B) ?_
  obtain ⟨f, hf, hval⟩ := exists_minimal_surface M (fun v => A v || B v)
  have hUsym : ∀ x y, M.weight x y ≠ 0 → U y = U x := by
    intro x y hw
    by_contra hne
    cases hx : U x with
    | true =>
      have hy : U y = false := by
        cases hy' : U y with
        | true => exact absurd (hy'.trans hx.symm) hne
        | false => rfl
      exact hw (hU x y hx hy)
    | false =>
      have hy : U y = true := by
        cases hy' : U y with
        | true => rfl
        | false => exact absurd (hy'.trans hx.symm) hne
      exact hw ((M.weight_symm x y).trans (hU y x hy hx))
  have hfA : Admissible M A (fun v => f v && U v) := by
    intro v hv
    show (f v && U v) = A v
    rw [hf v hv]
    have h1 := hA v
    have h2 := hB v
    cases hAv : A v <;> cases hBv : B v <;> simp_all
  have hfB : Admissible M B (fun v => f v && !(U v)) := by
    intro v hv
    show (f v && !(U v)) = B v
    rw [hf v hv]
    have h1 := hA v
    have h2 := hB v
    cases hAv : A v <;> cases hBv : B v <;> simp_all
  have key : cutWeight M.toBulkGraph (fun v => f v && U v)
      + cutWeight M.toBulkGraph (fun v => f v && !(U v))
      ≤ cutWeight M.toBulkGraph f := by
    have hcomb := cutWeight_comb M.toBulkGraph ![f]
      ![fun v => f v && U v, fun v => f v && !(U v)]
      (by
        intro x y hw
        have hxy := hUsym x y hw
        simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        cases hx : U x <;> rw [hx] at hxy <;> simp [hxy])
    simpa [Fin.sum_univ_two, Fin.sum_univ_one] using hcomb
  have e1 := entropy_le_of_admissible hfA
  have e2 := entropy_le_of_admissible hfB
  rw [hval]
  linarith
