-- Prove2me | Theorems.Thm_finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- name    : finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:18.234506+00:00
-- url     : https://prove2.me/theorems/7dbfab65-b7f6-4028-843f-b7ca49e7307a
-- title:
--   Finite hereditary properties admit maximal extensions
-- statement:
--   For a finite type with a reflexive, transitive, antisymmetric relation, every element satisfying a downward-hereditary property has a maximal feasible extension, and any relation-monotone natural-number score does not decrease. This removes the finite extremal-choice argument from the graph theorem. Independently, one can select a maximal element from the finite nonempty subtype of feasible extensions of x; transitivity keeps every further feasible extension in that subtype, heredity makes the feasibility condition appropriate, and score monotonicity supplies the score inequality. The parent instantiates α with SimpleGraph V, r with graph inclusion, P with HasPlanarDrawingOn, and score with edge-set ncard. The remaining parent work is to provide the standard relation laws and edge-count monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
    {α : Type} [Fintype α] (r : α → α → Prop) (P : α → Prop)
    (score : α → Nat)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hantisymm : ∀ a b, r a b → r b a → a = b)
    (hhered : ∀ a b, r b a → P a → P b)
    (hscore : ∀ a b, r a b → score a ≤ score b)
    (x : α) (hx : P x) :
    ∃ y, r x y ∧ P y ∧ score x ≤ score y ∧ ∀ z, r y z → P z → z = y := by
  sorry
