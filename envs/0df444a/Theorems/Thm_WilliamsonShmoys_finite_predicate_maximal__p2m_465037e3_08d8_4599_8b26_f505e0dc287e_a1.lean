-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a1
-- name    : WilliamsonShmoys.finite_predicate_maximal__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:10.281204+00:00
-- url     : https://prove2.me/theorems/48a0dda4-2fbc-4b99-b684-d61e828d3b92
-- title:
--   Maximal predicate witness on a finite type
-- statement:
--   For a finite type, if a predicate has a witness and every distinct related extension strictly increases a natural-valued measure, then some predicate witness has no distinct predicate witness related above it. This separates finite optimization from the graph-specific facts. Prove it by maximizing m over the finite nonempty set of elements satisfying P, then use hstrict to rule out any distinct related witness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_maximal__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a1
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (m : α → Nat)
    (hstrict : ∀ a b : α, R a b → a ≠ b → m a < m b)
    (P : α → Prop)
    (a₀ : α)
    (ha₀ : P a₀) :
    ∃ a : α, P a ∧ ∀ b : α, R a b → P b → b = a := by sorry
