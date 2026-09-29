-- Prove2me | solution 1 for EndpointCubeSkeleta.card_centers_le_card_points_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:30:06.35951+00:00
-- url     : https://prove2.me/submissions/28d97fba-734c-4344-be59-7e15678461c0

-- Sol generated from Cryptography/EndpointCubeSkeleta/OneDimensional.lean
import Mathlib
import Definitions.Def_Cryptography_EndpointCubeSkeleta_OneDimensional
/-
# Endpoint cardinality for one-dimensional discrete cube skeleta

This file formalizes the sharp counting mechanism behind the `n = 1, k = 0`
case of the endpoint-cardinality problem.  A zero-dimensional skeleton about an
integer center consists of the two endpoints `c-r` and `c+r`, with `r > 0`.
Recording those labelled endpoints is injective because their sum determines
the center.  Consequently, a finite endpoint set `B` covering a finite center
set `C` satisfies `|C| ≤ |B|²`.

The final theorem refutes the tempting stronger conjecture `|C| ≤ |B|`: four
carefully spaced endpoints cover six distinct centers.
-/

open EndpointCubeSkeleta

open Finset


/-- A choice of labelled endpoint pairs whose midpoint is the center is injective.
This is the midpoint estimate in its most elementary discrete form. -/
theorem labelled_endpoints_injective
    {centers : Finset ℤ} (left right : ℤ → ℤ)
    (hsum : ∀ c ∈ centers, left c + right c = 2 * c) :
    Set.InjOn (fun c => (left c, right c)) (↑centers : Set ℤ) := by
  intro a ha b hb hab
  have hl : left a = left b := congrArg Prod.fst hab
  have hr : right a = right b := congrArg Prod.snd hab
  have ha' := hsum a ha
  have hb' := hsum b hb
  omega








open EndpointCubeSkeleta in
theorem solution    {points centers : Finset ℤ} (hcover : EndpointCovered points centers) :
    centers.card ≤ points.card ^ 2 := by
  classical
  let rad (c : ℤ) : ℕ :=
    if hc : c ∈ centers then Classical.choose (hcover c hc) else 0
  let left (c : ℤ) : ℤ := c - (rad c : ℤ)
  let right (c : ℤ) : ℤ := c + (rad c : ℤ)
  have hrad (c : ℤ) (hc : c ∈ centers) :
      0 < rad c ∧ left c ∈ points ∧ right c ∈ points := by
    have hs := Classical.choose_spec (hcover c hc)
    simpa [rad, left, right, hc] using hs
  have hsum : ∀ c ∈ centers, left c + right c = 2 * c := by
    intro c hc
    simp [left, right]
    ring
  have hmap : Set.MapsTo (fun c => (left c, right c))
      (↑centers : Set ℤ) (↑(points ×ˢ points) : Set (ℤ × ℤ)) := by
    intro c hc
    exact Finset.mem_product.mpr ⟨(hrad c hc).2.1, (hrad c hc).2.2⟩
  have hinj := labelled_endpoints_injective left right hsum
  calc
    centers.card ≤ (points ×ˢ points).card :=
      Finset.card_le_card_of_injOn _ hmap hinj
    _ = points.card * points.card := Finset.card_product _ _
    _ = points.card ^ 2 := by ring
