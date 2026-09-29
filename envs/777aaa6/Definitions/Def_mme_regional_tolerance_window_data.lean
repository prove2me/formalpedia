-- Prove2me | Definitions.Def_mme_regional_tolerance_window_data
-- name    : mme_regional_tolerance_window_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-21T21:18:18.600688+00:00
-- url     : https://prove2.me/theorems/91b3529d-4537-4d7e-9c97-592992f4a9db
-- title:
--   Regional child and parent tolerance windows with explicit loss budgets
-- statement:
--   Definitions of physical child-frequency tolerance windows, their common parent-mixture windows, and the explicit finite logarithmic copy budget for varying admissible exact profiles. This data does not assume a tensor map, type cover, or successful numerical budget.
-- source:
--   Finite-profile tolerance-band construction for the More Asymmetry recursion.

import Definitions.Def_mme_regional_certified_log_copy_bound
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells
set_option autoImplicit false
namespace MME.RegionRealization

abbrev WindowProfile {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) :=
  Fin 3 → Cell D.half D.R D.parent → CompleteSplit.CompleteWord ell → ℕ

/-- Exact finite profile requirements, prior to choosing extraction data. -/
def WindowAdmissible {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (mu : WindowProfile D) : Prop :=
  (∀ i c, ∑ w, mu i c w = D.m c.1 c.2 + D.m c.1 (complement (D.total c.1) c.2)) ∧
  (∀ i c w, 0 < mu i c w → ∑ r, (w r).val = (c.2.val i).val) ∧ BoundaryProfiles mu

noncomputable def WindowClose {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (delta : ℝ) (i : Fin 3) (mu : Cell D.half D.R D.parent → CompleteSplit.CompleteWord ell → ℕ) : Prop :=
  ∀ c w, |cellFrequency mu c w - cellFrequency (D.mu i) c w| ≤ delta

/-- Graded child words in a closed cell-frequency tolerance band. -/
noncomputable def childWindow {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (delta : ℝ) : Predicate M := fun i x ↦
  Graded D.total i D.reference (split D.positions D.length x) ∧
    WindowClose D delta i (count (fullCell D.total D.reference) (split D.positions D.length x))

/-- Parent empirical pair frequencies around the central induced mixture. -/
noncomputable def parentWindow {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (eta : ℝ) : Predicate M := fun i x ↦
  parentTypical D.total D.n D.m (D.mu i) eta (split D.positions D.length x)

/-- The explicit certified scalar budget evaluated at a varying exact profile.
All finite losses are retained, including profile-dependent hole repair. -/
noncomputable def windowLogBudget {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (mu : WindowProfile D) (eps : ℝ) : ℝ :=
  let capacity := ∏ i : Fin 3, Nat.card (Block ell (fullCell D.total D.reference)
    (fun c i ↦ (c.2.val i).val) mu i)
  let repairExponent := Nat.log D.repairScale capacity + 1
  let E := RegionRate.regionalRate D.total D.n D.m mu
  let loss := ((∑ r, D.n r : ℕ) : ℝ) *
    RegionRate.entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
  let theta := RegionRate.scaleExponent D.total D.n D.m mu eps
  let factor := RegionRate.scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell
  E - loss - 4 * Real.sqrt (Real.log factor + theta) -
    Real.log (64 * RegionRate.polynomialFactor D.n
      (Fintype.card (Cell D.half D.R D.parent)) * factor) - repairExponent * Real.log 8

end MME.RegionRealization


