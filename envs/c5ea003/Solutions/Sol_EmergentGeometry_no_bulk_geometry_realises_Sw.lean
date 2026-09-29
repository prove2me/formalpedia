-- Prove2me | solution 1 for EmergentGeometry.no_bulk_geometry_realises_Sw
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:01:05.978757+00:00
-- url     : https://prove2.me/submissions/486d694a-9905-490e-97e1-f6b2b4a2391c

-- Sol generated from Novelty/CyclicIndependence.lean
import Mathlib
import Definitions.Def_Novelty_CyclicIndependence
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality
import Theorems.Thm_EmergentGeometry_entropy_cyclic5

/-!
# Independence of the five-party cyclic inequality, and a non-geometric entropy vector

`Novelty.HolographicCyclicInequality` proves that every min-cut ("holographic")
entropy assignment obeys the five-party cyclic inequality

`∑_j S(A_j A_{j+1}) + S(A₀A₁A₂A₃A₄) ≤ ∑_j S(A_j A_{j+1} A_{j+2})`.

This file establishes that this inequality is *not* a formal consequence of the
standard entropy inequalities available before it, namely

* **subadditivity** `S(XY) ≤ S(X) + S(Y)`,
* **strong subadditivity** `S(XYZ) + S(Y) ≤ S(XY) + S(YZ)`,
* **weak monotonicity** `S(X) + S(Z) ≤ S(XY) + S(YZ)`, and
* **monogamy of mutual information (MMI)**
  `S(XY) + S(YZ) + S(XZ) ≥ S(XYZ) + S(X) + S(Y) + S(Z)`,

by exhibiting an explicit integer-valued five-party entropy vector `Sw` that
satisfies all four families on all pairwise disjoint arguments, yet violates the
cyclic inequality by exactly `1`.

Subsets of the five parties are encoded as bitmasks `0 ≤ m < 32`; unions become
`|||` and disjointness becomes `&&& = 0`.  All four validity families are
verified by kernel evaluation over the full `32³ = 32768` case space of triples
of masks — this is a genuine exhaustive computation, not a definitional
unfolding.

The consequence for emergent geometry: **no** bulk graph whatsoever can produce
this entropy vector (`no_bulk_geometry_realises_Sw`).  So the geometric states
form a strictly smaller cone than the quantum-mechanically consistent ones, and
"reconstruct the geometry from the entanglement" has a genuine obstruction that
is invisible to subadditivity, SSA, weak monotonicity and monogamy alone.
-/

noncomputable section

open EmergentGeometry

open Finset

/-! ## The witness vector -/



/-! ## The four validity families

Each is checked exhaustively over all masks below `32`. -/






/-! ## Packaging the independence statement -/







/-! ## No bulk geometry realises the witness -/

variable {V : Type*} [Fintype V] [DecidableEq V]





open EmergentGeometry in
theorem solution(M : HoloModel V) (A₀ A₁ A₂ A₃ A₄ : Region V)
    (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v))
    (hreal : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
      entropy M (unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄) = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ)) :
    False := by
  have hE : ∀ (b₀ b₁ b₂ b₃ b₄ : Bool) (R : Region V),
      (∀ v, unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄ v = R v) →
      entropy M R = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ) := by
    intro b₀ b₁ b₂ b₃ b₄ R h
    have hR : R = unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄ := funext fun v => (h v).symm
    rw [hR]; exact hreal b₀ b₁ b₂ b₃ b₄
  have e01 := hE true true false false false (fun v => A₀ v || A₁ v)
    (by intro v; simp [unionSel])
  have e12 := hE false true true false false (fun v => A₁ v || A₂ v)
    (by intro v; simp [unionSel])
  have e23 := hE false false true true false (fun v => A₂ v || A₃ v)
    (by intro v; simp [unionSel])
  have e34 := hE false false false true true (fun v => A₃ v || A₄ v)
    (by intro v; simp [unionSel])
  have e40 := hE true false false false true (fun v => A₄ v || A₀ v)
    (by intro v; simp [unionSel]; cases A₀ v <;> cases A₄ v <;> rfl)
  have eall := hE true true true true true (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
    (by intro v; simp [unionSel])
  have t012 := hE true true true false false (fun v => A₀ v || A₁ v || A₂ v)
    (by intro v; simp [unionSel])
  have t123 := hE false true true true false (fun v => A₁ v || A₂ v || A₃ v)
    (by intro v; simp [unionSel])
  have t234 := hE false false true true true (fun v => A₂ v || A₃ v || A₄ v)
    (by intro v; simp [unionSel])
  have t340 := hE true false false true true (fun v => A₃ v || A₄ v || A₀ v)
    (by intro v; simp [unionSel]; cases A₀ v <;> cases A₃ v <;> cases A₄ v <;> rfl)
  have t401 := hE true true false false true (fun v => A₄ v || A₀ v || A₁ v)
    (by intro v; simp [unionSel]; cases A₀ v <;> cases A₁ v <;> cases A₄ v <;> rfl)
  have hcyc := entropy_cyclic5 M A₀ A₁ A₂ A₃ A₄ hd
  rw [e01, e12, e23, e34, e40, eall, t012, t123, t234, t340, t401] at hcyc
  norm_num [bmask, Sw] at hcyc
