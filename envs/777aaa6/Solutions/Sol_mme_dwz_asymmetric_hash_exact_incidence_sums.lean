-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_exact_incidence_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:03:20.115347+00:00
-- url     : https://prove2.me/submissions/4b6f7d58-cc2c-428f-9135-e1a1279a1a79

import Mathlib
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators

set_option autoImplicit false
set_option warningAsError true

/-!
# Exact double counting for the DWZ asymmetric hash

This theorem packages the two local hash-fiber calculations into the global
first and collision moments.  Its collision universe is directed from the
joint-profile target family to the full marginal-supported ambient family.
-/

theorem solution
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
  classical
  let C : Finset (Edge × Edge) :=
    (T.product A).filter (fun q ↦
      q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
  let Coll : Ω → Finset (Edge × Edge) := fun ω ↦
    (((T.filter (fun a ↦ a ∈ E ω)).product (E ω)).filter
      (fun q ↦ q.1 ≠ q.2 ∧
        (x q.1 = x q.2 ∨ y q.1 = y q.2)))
  have hColl (ω : Ω) :
      Coll ω = C.filter (fun q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω) := by
    ext q
    constructor
    · intro hq
      have hlocal := Finset.mem_filter.mp hq
      have hprod := Finset.mem_product.mp hlocal.1
      have htarget := Finset.mem_filter.mp hprod.1
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨
          Finset.mem_product.mpr ⟨htarget.1, hE ω hprod.2⟩,
          hlocal.2⟩,
        htarget.2, hprod.2⟩
    · intro hq
      have houter := Finset.mem_filter.mp hq
      have hglobal := Finset.mem_filter.mp houter.1
      have hprod := Finset.mem_product.mp hglobal.1
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨
          Finset.mem_filter.mpr ⟨hprod.1, houter.2.1⟩,
          houter.2.2⟩,
        hglobal.2⟩
  constructor
  · calc
      (∑ ω, (T.filter (fun a ↦ a ∈ E ω)).card) =
          ∑ a ∈ T, (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card := by
            simpa using mme_finset_incidence_double_count
              (Finset.univ : Finset Ω) T (fun ω a ↦ a ∈ E ω)
      _ = ∑ _a ∈ T, B * p ^ (N + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsingle a ha
      _ = T.card * B * p ^ (N + 1) := by simp [mul_assoc]
  · change (∑ ω, (Coll ω).card) ≤ C.card * B * p ^ N
    calc
      (∑ ω, (Coll ω).card) =
          ∑ ω, (C.filter (fun q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω)).card := by
            apply Finset.sum_congr rfl
            intro ω hω
            exact congrArg Finset.card (hColl ω)
      _ = ∑ q ∈ C,
          (Finset.univ.filter (fun ω : Ω ↦
            q.1 ∈ E ω ∧ q.2 ∈ E ω)).card := by
            simpa using mme_finset_incidence_double_count
              (Finset.univ : Finset Ω) C
                (fun ω q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω)
      _ ≤ ∑ _q ∈ C, B * p ^ N := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpair q hq
      _ = C.card * B * p ^ N := by simp [mul_assoc]

