-- Prove2me | solution 1 for mme_type2_fractional_retention_of_relative_mode_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:35:49.016362+00:00
-- url     : https://prove2.me/submissions/864f8d45-8d36-413c-b139-12d91e20fae8

import Mathlib
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

set_option autoImplicit false
set_option warningAsError true

/-- If the ambient mode degree is at most a factor `rho` above the exact
target mode degree, the uniform hash construction retains an `ell` fraction
of the entire target family under the normalized Behrend margin. -/
theorem solution
    {State Edge : Type} {Vertex : Fin 3 → Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambientAll targetAll : Finset Edge)
    (retain : State → Edge → Prop) [DecidableRel retain]
    (P B Q D Dstar : ℕ) (V rho ell : ℝ)
    (hV : 0 ≤ V)
    (hstate : Fintype.card State = P * Q)
    (htargetCard : (targetAll.card : ℝ) = V * (Dstar : ℝ))
    (hdegree : ∀ i : Fin 3, ∀ a ∈ targetAll,
      (ambientAll.filter (fun b ↦ vertex i b = vertex i a)).card ≤ D)
    (hdegreeRatio : (D : ℝ) ≤ rho * (Dstar : ℝ))
    (hedge : ∀ a ∈ targetAll,
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω a)).card = B * Q)
    (hpair : ∀ ab ∈ ((targetAll ×ˢ ambientAll).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)),
      ((Finset.univ : Finset State).filter
        (fun ω ↦ retain ω ab.1 ∧ retain ω ab.2)).card ≤ Q)
    (htargetAmbient : targetAll ⊆ ambientAll)
    (hclosure : ∀ ω,
      ∀ x ∈ targetAll.filter (retain ω),
      ∀ y ∈ targetAll.filter (retain ω),
      ∀ z ∈ targetAll.filter (retain ω),
        supportedMix x y z →
          ∃ e ∈ ambientAll.filter (retain ω),
            vertex 0 e = vertex 0 x ∧
            vertex 1 e = vertex 1 y ∧
            vertex 2 e = vertex 2 z)
    (hmargin :
      (P : ℝ) * ell + 3 * rho * (Dstar : ℝ) ≤ (B : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ targetAll.filter (retain ω) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      (targetAll.card : ℝ) * ell ≤ (kept.card : ℝ) := by
  have hdegScaled :
      3 * (Dstar : ℝ) * (D : ℝ) ≤
        3 * (Dstar : ℝ) * (rho * (Dstar : ℝ)) :=
    mul_le_mul_of_nonneg_left hdegreeRatio (by positivity)
  have hmarginScaled :=
    mul_le_mul_of_nonneg_left hmargin (Nat.cast_nonneg Dstar)
  have hmargin' :
      (P : ℝ) * ((Dstar : ℝ) * ell) +
          3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (B : ℝ) := by
    calc
      (P : ℝ) * ((Dstar : ℝ) * ell) +
          3 * (Dstar : ℝ) * (D : ℝ) ≤
          (P : ℝ) * ((Dstar : ℝ) * ell) +
            3 * (Dstar : ℝ) * (rho * (Dstar : ℝ)) :=
        by simpa [add_comm] using
          (add_le_add_left hdegScaled
            ((P : ℝ) * ((Dstar : ℝ) * ell)))
      _ = (Dstar : ℝ) *
          ((P : ℝ) * ell + 3 * rho * (Dstar : ℝ)) := by ring
      _ ≤ (Dstar : ℝ) * (B : ℝ) := hmarginScaled
  obtain ⟨ω, kept, hkept, hinj, hdiag, hcard⟩ :=
    mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      vertex supportedMix ambientAll targetAll retain
      P B Q D Dstar V ((Dstar : ℝ) * ell)
      hV hstate htargetCard hdegree hedge hpair
      htargetAmbient hclosure hmargin'
  refine ⟨ω, kept, hkept, hinj, hdiag, ?_⟩
  calc
    (targetAll.card : ℝ) * ell =
        (V * (Dstar : ℝ)) * ell := by rw [htargetCard]
    _ = V * ((Dstar : ℝ) * ell) := by ring
    _ ≤ (kept.card : ℝ) := hcard
