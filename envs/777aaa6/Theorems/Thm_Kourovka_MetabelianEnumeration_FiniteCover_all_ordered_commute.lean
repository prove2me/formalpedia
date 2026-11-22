-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_all_ordered_commute
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.all_ordered_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:40.473494+00:00
-- url     : https://prove2.me/theorems/fe473571-7ffd-45fd-8146-11bbb51f6a11
-- title:
--   Finite Cover: all ordered commute
-- statement:
--   Repeated uniform radius increases prove every ordered commutator relation.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L99-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean#L99-L127

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.all_ordered_commute {k a : ℕ} (data : Datum k a) (t : Fin k → G) (A : Fin a → G)
    (hk : 1 ≤ k) (C D R δ : ℝ)
    (hC : 0 < C) (hRk : 2 * (k : ℝ) < R) (hRD : 2 * (k : ℝ) * D < R)
    (hRC : C < R) (hRD2 : D ^ 2 < C * R)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball R → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)) := by sorry
