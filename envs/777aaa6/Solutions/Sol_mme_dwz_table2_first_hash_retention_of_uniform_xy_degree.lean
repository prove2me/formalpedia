-- Prove2me | solution 1 for mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:49:16.500954+00:00
-- url     : https://prove2.me/submissions/a9a906b2-48de-45b1-ad33-38d8807e2899

import Theorems.Thm_mme_dwz_asymmetric_hash_retention_from_exact_fibers
import Theorems.Thm_mme_dwz_table2_affine_hash_incidence_factory

set_option autoImplicit false
set_option warningAsError true

open MME

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d : ℕ) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeX (b t)) =
          (fun t ↦ MME.DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeY (b t)) =
          (fun t ↦ MME.DWZSquare.shapeY (a t)))).card ≤ d) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    ∃ E : Ω → Finset Edge,
      (∀ q, E q ⊆ A) ∧
      ∃ q : Ω, ∃ I : Finset Edge,
        I ⊆ T ∧
        I ⊆ E q ∧
        (∀ e ∈ I, ∀ e' ∈ E q,
          x e = x e' ∨ y e = y e' → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  dsimp only
  have hfactory := mme_dwz_table2_affine_hash_incidence_factory
    hpodd hp5 S hSrange hSfree A T hTA
  dsimp only at hfactory
  obtain ⟨hstate, E, hE, hsingle, hpair⟩ := hfactory
  have hp : 0 < p := by omega
  obtain ⟨q, I, hIT, hIE, hisolated, hcard⟩ :=
    mme_dwz_asymmetric_hash_retention_from_exact_fibers
      A T
      (fun w t ↦ MME.DWZSquare.shapeX (w t))
      (fun w t ↦ MME.DWZSquare.shapeY (w t))
      E N p S.card d hp hmod hE hx hy hstate hsingle hpair
  exact ⟨E, hE, q, I, hIT, hIE, hisolated, hcard⟩

