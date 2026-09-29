-- Prove2me | solution 1 for EmergentGeometry.mutualInfo_eq_zero_of_no_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:57:18.427784+00:00
-- url     : https://prove2.me/submissions/c33c19af-2df5-415b-ac9e-c8134a336ebf

-- Sol generated from Novelty/EREPRBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_entropy_additive_of_split

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
theorem solution{M : HoloModel V} (A B : Region V)
    (h : ∀ u v, A u = true → B v = true → ¬ BulkPath M.toBulkGraph u v) :
    mutualInfo M A B = 0 := by
  classical
  set U : Region V :=
    fun x => if ∃ a, A a = true ∧ BulkPath M.toBulkGraph a x then true else false with hUdef
  have hUclosed : ∀ x y, U x = true → U y = false → M.weight x y = 0 := by
    intro x y hx hy
    by_contra hw
    have hpos : 0 < M.weight x y :=
      lt_of_le_of_ne (M.weight_nonneg x y) (Ne.symm hw)
    have hPx : ∃ a, A a = true ∧ BulkPath M.toBulkGraph a x := by
      by_contra hcon
      rw [hUdef] at hx
      simp [hcon] at hx
    have hPy : ¬ ∃ b, A b = true ∧ BulkPath M.toBulkGraph b y := by
      intro hcon
      rw [hUdef] at hy
      simp [hcon] at hy
    obtain ⟨a, ha, hpath⟩ := hPx
    exact hPy ⟨a, ha, hpath.tail hpos⟩
  have hAU : ∀ v, A v = true → U v = true := by
    intro v hv
    rw [hUdef]
    exact if_pos ⟨v, hv, Relation.ReflTransGen.refl⟩
  have hBU : ∀ v, B v = true → U v = false := by
    intro v hv
    rw [hUdef]
    refine if_neg ?_
    rintro ⟨a, ha, hpath⟩
    exact h a v ha hv hpath
  have hadd := entropy_additive_of_split hUclosed A B hAU hBU
  simp only [mutualInfo, hadd]
  ring
