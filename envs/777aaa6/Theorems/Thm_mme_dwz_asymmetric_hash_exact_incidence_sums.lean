-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_exact_incidence_sums
-- name    : mme_dwz_asymmetric_hash_exact_incidence_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:01:40.93429+00:00
-- url     : https://prove2.me/theorems/5530552e-22e4-42c9-aa41-85c49dfb20f7
-- title:
--   Exact affine single-edge and collision incidence sums
-- statement:
--   Suppose each target edge lies in exactly B p^(N+1) hash states, while every directed target–ambient X/Y-collision pair lies in at most B p^N common states. Then the total number of retained target incidences is exactly |T|B p^(N+1), and the total local collision count is at most the global directed collision count times B p^N. This is the double-counting bridge from local affine fibers to the global moments used in weighted isolation.
-- source:
--   Duan--Wu--Zhou asymmetric hashing, exact affine-fiber double counting around Equation (21).

import Mathlib
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators

set_option autoImplicit false

/-!
# Exact double counting for the DWZ asymmetric hash

This theorem packages the two local hash-fiber calculations into the global
first and collision moments.  Its collision universe is directed from the
joint-profile target family to the full marginal-supported ambient family.
-/

theorem mme_dwz_asymmetric_hash_exact_incidence_sums
    {Ω Edge X Y : Type}
    [Fintype Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (E : Ω → Finset Edge) (N p B : ℕ)
    (hE : ∀ ω, E ω ⊆ A)
    (hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
        B * p ^ (N + 1))
    (hpair : ∀ q ∈ (T.product A).filter (fun q ↦
        q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
      (Finset.univ.filter (fun ω : Ω ↦
        q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
          B * p ^ N) :
    (∑ ω, (T.filter (fun a ↦ a ∈ E ω)).card) =
        T.card * B * p ^ (N + 1) ∧
      (∑ ω, (((T.filter (fun a ↦ a ∈ E ω)).product (E ω)).filter
        (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card) ≤
        ((T.product A).filter (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card * B * p ^ N := by
  sorry
