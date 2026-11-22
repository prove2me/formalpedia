-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_radius_step
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.radius_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:28.362334+00:00
-- url     : https://prove2.me/theorems/33d6c6cb-447d-46d7-a995-5a78df04776f
-- title:
--   Finite Cover: radius step
-- statement:
--   A single uniform increase of radius follows from either sign of the
--   polynomial identity and the certified shrinking direction.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L45-L96
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L45-L96

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.radius_step {k a : ℕ} (data : Datum k a) (t : Fin k → G) (A : Fin a → G)
    (hk : 1 ≤ k) (C D ρ δ : ℝ)
    (hC : 0 < C) (hρk : 2 * (k : ℝ) < ρ) (hρD : 2 * (k : ℝ) * D < ρ)
    (hρC : C < ρ) (hρD2 : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, v ∈ ball (ρ + δ) → Commute (A p) (conjugate (A q) (orderedWord t v)) := by sorry
