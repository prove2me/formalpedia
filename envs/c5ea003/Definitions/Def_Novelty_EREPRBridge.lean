-- Prove2me | Definitions.Def_Novelty_EREPRBridge
-- name    : Novelty_EREPRBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:19:43.482734+00:00
-- url     : https://prove2.me/theorems/6e160098-3a57-4d34-a1b2-d5b3a183f78d
-- title:
--   Aether Catalog definitions — Novelty_EREPRBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EREPRBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EREPRBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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

namespace EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Boundary regions consisting of one or two cells -/

/-- The one-cell boundary region `{u}`. -/
def single (u : V) : Region V := fun x => decide (x = u)


/-- A model has no hidden bulk cells when every cell is a boundary cell. -/
def NoBulk (M : HoloModel V) : Prop := ∀ v, M.bdry v = true






/-! ## Bulk connectivity: Einstein–Rosen bridges -/

/-- Two bulk cells are adjacent when the geometry assigns them positive area. -/
def BulkAdj (G : BulkGraph V) (u v : V) : Prop := 0 < G.weight u v

/-- A bulk bridge: a chain of positive-area steps from `u` to `v`. -/
def BulkPath (G : BulkGraph V) : V → V → Prop := Relation.ReflTransGen (BulkAdj G)




/-! ## The single-throat geometry of a qubit pair -/

/-- The two-cell geometry with a single throat of weight `w`. -/
def pairModel (w : ℝ) (hw : 0 ≤ w) : HoloModel (Fin 2) where
  weight := fun u v => if u = v then 0 else w
  weight_symm := by
    intro u v
    by_cases h : u = v
    · simp [h]
    · simp [h, Ne.symm h]
  weight_nonneg := by
    intro u v
    by_cases h : u = v <;> simp [h, hw]
  bdry := fun _ => true




/-! ## Two-qubit states: entanglement is a bridge -/

open EmergentSpacetime






end EmergentGeometry


