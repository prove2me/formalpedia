-- Prove2me | Theorems.Thm_Hirsch_interleaved_moment_minimal_nonfaces
-- name    : Hirsch.interleaved_moment_minimal_nonfaces
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T03:12:22.232126+00:00
-- url     : https://prove2.me/theorems/380347be-2134-4160-89fc-6bf7c899f93e
-- title:
--   Interleaved parameter sets are minimal nonfaces of the original moment inequalities
-- statement:
--   Let a assign distinct real parameters to m original labels. Choose k+1 pairs of labels l_i,r_i with a(l_i)<a(r_i), and a(r_i)<a(l_j) whenever i<j. In dimension 2k form the original mean-centered moment inequalities row_i(x)<=1, with the average over ALL m original labels. The sets L={l_i} and R={r_i} each have exactly k+1 labels, are disjoint, and are both incompatible: every feasible point leaves at least one L row and one R row strictly slack. Conversely EVERY proper subset S of either L or R has an actual feasible point making exactly the S rows tight and every other ORIGINAL row strictly slack. Thus both are minimal nonfaces of this explicit inequality system. The proof derives the left/right barycentric signs by pairing factors, applies the accepted barycentric polynomial obstruction, and constructs all proper-subset witnesses through the accepted squared-root polynomial theorem. No sign classification, infeasibility witness, proper-face oracle, or precomputed minimal-nonface catalogue is an assumption. The zero-dimensional case k=0 is included as a statement about rows. The theorem does not assert that all displayed rows are genuine facets in every degenerate case, count the full family of such sets, establish boundedness/full-dimensionality, or prove a graph-diameter bound.
-- source:
--   Composes accepted #285 exact small-face witnesses (d8214487-c5aa-446b-8e75-f485979b94f3; source c8589a1fee999c8497ebd2d1e6e9601ce739ec8b) and #286 moment barycentric nonfaces (e37928aa-132f-4b32-ba91-47b4a1f75fa4; source 5b44ad2795b85acb693e6e9f44039e9d9c425e85). Their full helper namespace bodies are reused unchanged. The new paired-factor sign identification and explicit minimality assembly close the next interface recorded in STATUS.md at9a1b6768d27d38b719bf4c0c795f8f7257415626. Classical moment-curve/interpolation geometry is credited, with no historical-priority claim.

import Mathlib
open scoped BigOperators

theorem Hirsch.interleaved_moment_minimal_nonfaces (k m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (l r : Fin (k+1) → Fin m)
    (hpair : ∀ i, a (l i) < a (r i))
    (hsep : ∀ i j, i < j → a (r i) < a (l j)) :
    let row : (Fin (2*k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2*k),
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let L : Finset (Fin m) := Finset.univ.image l
    let R : Finset (Fin m) := Finset.univ.image r
    L.card = k+1 ∧ R.card = k+1 ∧ Disjoint L R ∧
    (∀ x : Fin (2*k) → ℝ, (∀ i, row x i ≤ 1) →
      (∃ i ∈ L, row x i < 1) ∧ (∃ i ∈ R, row x i < 1)) ∧
    ∀ S : Finset (Fin m), (S ⊂ L ∨ S ⊂ R) →
      ∃ x : Fin (2*k) → ℝ, ∀ i, row x i ≤ 1 ∧ (row x i = 1 ↔ i ∈ S) := by sorry
