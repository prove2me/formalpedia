-- Prove2me | Definitions.Def_mme_mixed_depth_profile_certificate
-- name    : mme_mixed_depth_profile_certificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-01T09:30:16.646994+00:00
-- url     : https://prove2.me/theorems/7765bcb3-98a2-4c40-a8a0-e91f197ec205
-- title:
--   Finite profile trees with early boundary leaves and regional routing
-- statement:
--   This interface describes finite spatial trees for recursive CW extraction. A boundary leaf at level $\ell$ contains integer word counts supported on a fixed free-mode grade, a zero-mode orientation, and layouts of its $k^2$ replicas. An elementary positive branch contains the existing feasible regional profile packets. Other nodes descend through a regional layer or partition physical positions among branches at the same level.
--
--   Each node has a finite observation window: actual word counts or parent-pair frequencies, fixed central values, and physical coordinate-grade conditions. A routing certificate expresses the preceding layer's word counts and centers as finite nonnegative weighted sums of child observations and transports coordinate grades. Its finite row bound is independent of $k$ and need not equal one.
--
--   The interface computes a fixed input-degree budget, an additive extraction rate, and a volume rate. Boundary leaves contribute their histogram entropy and CW-letter terms; elementary branches contribute half their total grade-one multiplicity times $\log 5$. Partitions add these quantities, and regional descent adds extraction rates while retaining terminal volume rates.
--
--   No actual extraction stage, terminal recipe, window inclusion or matrix-size estimate is a field. Empty spatial families and zero-length boundary leaves are allowed. The interface supports branches terminating at different recursive levels, including the level-four application. Concrete AlphaEvolve profile values and a final strict numerical surplus are separate obligations.
-- source:
--   Finite certificate interface for assembling early boundary branches with the graded regional profile compiler. Uses mme_regional_profile_layer_compiler_data and the existing Boundary.Profile interface. Application context: https://arxiv.org/html/2608.16884v1, Sections 2.3–2.4.

import Definitions.Def_mme_regional_profile_layer_compiler_data
import Definitions.Def_mme_modern_entropy_data

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.ProfiledCW
  MME.RegionRealization MME.ProfileCompiler MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace MME.MixedCompiler

/-- A finite family of actual word observations and coordinate grades. -/
structure Window (N : ℕ → ℕ) where
  Obs : Type
  finiteObs : Fintype Obs
  grade : ∀ k, Fin 3 → FineWord (N k) → Prop
  observe : ∀ k, Fin 3 → FineWord (N k) → Obs → ℝ
  center : Fin 3 → Obs → ℝ

attribute [instance] Window.finiteObs

def Window.source {N : ℕ → ℕ} (W : Window N) (eps : ℝ) (k : ℕ) : Predicate (N k) :=
  fun i x ↦ W.grade k i x ∧ ∀ o, |W.observe k i x o - W.center i o| < eps

noncomputable def layerWindow {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) : Window N where
  Obs := L.Observations
  finiteObs := inferInstance
  grade := fun k i x ↦ ∀ j, ParentGraded (L.packet j).parent
    (fun r ↦ k ^ 2 * (L.packet j).n r) i ((L.packet j).words k (L.piece k x j))
  observe := fun k _ x o ↦ L.observe k x o
  center := L.center

noncomputable def Window.partition {N : ℕ → ℕ} {parts : ℕ}
    (Ns : Fin parts → ℕ → ℕ)
    (positions : ∀ k, (Σ j, Fin (Ns j k)) ≃ Fin (N k))
    (Ws : ∀ j, Window (Ns j)) : Window N where
  Obs := Σ j, (Ws j).Obs
  finiteObs := inferInstance
  grade := fun k i x ↦ ∀ j, (Ws j).grade k i (fun r ↦ x (positions k ⟨j,r⟩))
  observe := fun k i x o ↦ (Ws o.1).observe k i
    (fun r ↦ x (positions k ⟨o.1,r⟩)) o.2
  center := fun i o ↦ (Ws o.1).center i o.2

/-- Early leaves contain finite integer boundary profiles and their physical
positions, not terminal recipes or matrix-size estimates. -/
structure BoundaryLayer (ell : ℕ) (N : ℕ → ℕ) where
  parts : ℕ
  length : Fin parts → ℕ
  profile : ∀ j, Boundary.Profile ell (length j)
  zeroMode : Fin parts → Fin 3
  positions : ∀ k, (Σ j, Fin (length j * k ^ 2 * 2 ^ (ell - 1))) ≃ Fin (N k)

def BoundaryLayer.piece {ell : ℕ} {N : ℕ → ℕ} (B : BoundaryLayer ell N)
    (k : ℕ) (x : FineWord (N k)) (j : Fin B.parts) :
    FineWord (B.length j * k ^ 2 * 2 ^ (ell - 1)) :=
  fun r ↦ x (B.positions k ⟨j,r⟩)

def BoundaryLayer.words {ell : ℕ} {N : ℕ → ℕ} (B : BoundaryLayer ell N)
    (k : ℕ) (x : FineWord (N k)) (j : Fin B.parts) :
    Fin (B.length j * k ^ 2) → CompleteWord ell :=
  split (Equiv.refl _) rfl (B.piece k x j)

noncomputable def BoundaryLayer.window {ell : ℕ} {N : ℕ → ℕ}
    (B : BoundaryLayer ell N) : Window N where
  Obs := Fin B.parts × CompleteWord ell
  finiteObs := inferInstance
  grade := fun k i x ↦ ∀ j p, grade (B.words k x j p) = (B.profile j).shape (B.zeroMode j) i
  observe := fun k _ x o ↦
    (count (fun _ : Fin (B.length o.1 * k ^ 2) ↦ ()) (B.words k x o.1) () o.2 : ℝ) /
      (k ^ 2 : ℕ)
  center := fun i o ↦ ((B.profile o.1).mu (B.zeroMode o.1) i o.2 : ℝ)

noncomputable def BoundaryLayer.volumeRate {ell : ℕ} {N : ℕ → ℕ}
    (B : BoundaryLayer ell N) : ℝ :=
  ∑ j, if B.length j = 0 then 0 else
    (B.length j : ℝ) * Real.log 2 *
      mme_modern_entropyBits (fun w ↦ ((B.profile j).count w : ℝ) / B.length j) +
      ((∑ w, (B.profile j).count w * Boundary.ones w : ℕ) : ℝ) * Real.log 5

/-- Routing is expressed by finite count identities, central values, and
coordinate grades. The row bound need not be one or depend on scale. -/
structure Routing {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) (W : Window N) where
  weight : ∀ i j, (L.packet j).Cells → CompleteWord ell → W.Obs → ℝ
  nonneg : ∀ i j c w o, 0 ≤ weight i j c w o
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  row_le : ∀ i j c w, ∑ o, weight i j c w o ≤ bound
  count_identity : ∀ k i (x : FineWord (N k)) j c w,
    ((L.packet j).histogram k (L.piece k x j) c w : ℝ) =
      ((k ^ 2 * (L.packet j).mass c : ℕ) : ℝ) *
        ∑ o, weight i j c w o * W.observe k i x o
  center_identity : ∀ i j c w, ((L.packet j).mu i c w : ℝ) =
    ((L.packet j).mass c : ℝ) * ∑ o, weight i j c w o * W.center i o
  grade_identity : ∀ k i (x : FineWord (N k)), W.grade k i x →
    ∀ j, Graded (L.packet j).total i ((L.packet j).address k)
      ((L.packet j).words k (L.piece k x j))

/-- A finite tree may stop boundary branches at their current level and recurse
on other branches. Every constructor records only finite profile/layout data. -/
inductive Certificate : (ell : ℕ) → (N : ℕ → ℕ) → Window N → Type 1
  | boundary {ell N} (B : BoundaryLayer ell N) : Certificate ell N B.window
  | elementary {N} (L : Layer 1 N) : Certificate 2 N (layerWindow L)
  | descend {ell N W} (L : Layer ell N) (next : Certificate ell N W)
      (routing : Routing L W) : Certificate (ell + 1) N (layerWindow L)
  | partition {ell N parts} (Ns : Fin parts → ℕ → ℕ)
      (positions : ∀ k, (Σ j, Fin (Ns j k)) ≃ Fin (N k))
      {Ws : ∀ j, Window (Ns j)} (children : ∀ j, Certificate ell (Ns j) (Ws j)) :
      Certificate ell N (Window.partition Ns positions Ws)

def Certificate.degree {ell N W} : Certificate ell N W → ℕ
  | .boundary _ => 0
  | .elementary _ => 0
  | .descend L next _ => L.degree + next.degree
  | .partition _ _ children => ∑ j, (children j).degree

noncomputable def Certificate.rate {ell N W} : Certificate ell N W → ℝ
  | .boundary _ => 0
  | .elementary L => L.rate
  | .descend L next _ => L.rate + next.rate
  | .partition _ _ children => ∑ j, (children j).rate

noncomputable def Certificate.volumeRate {ell N W} : Certificate ell N W → ℝ
  | .boundary B => B.volumeRate
  | .elementary L =>
      (((∑ j, ∑ i : Fin 3, ∑ c, (L.packet j).mu i c (fun _ ↦ 1) : ℕ) : ℝ) / 2) * Real.log 5
  | .descend _ next _ => next.volumeRate
  | .partition _ _ children => ∑ j, (children j).volumeRate

end MME.MixedCompiler


