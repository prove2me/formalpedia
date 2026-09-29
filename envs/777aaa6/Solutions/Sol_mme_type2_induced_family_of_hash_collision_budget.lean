-- Prove2me | solution 1 for mme_type2_induced_family_of_hash_collision_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:27:24.127135+00:00
-- url     : https://prove2.me/submissions/fdb7d6c4-1a60-4569-9c7d-d1109876883a

import Mathlib
import Theorems.Thm_mme_finite_collision_budget_averaging_real
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
    {State : Type} {Edge : Type*} {Vertex : Fin 3 → Type*}
    [Fintype State] [Nonempty State]
    [DecidableEq Edge] [∀ i, DecidableEq (Vertex i)]
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target : State → Finset Edge)
    (htarget : ∀ ω, target ω ⊆ ambient ω)
    (hclosure : ∀ ω, ∀ x ∈ target ω, ∀ y ∈ target ω,
      ∀ z ∈ target ω, supportedMix x y z →
        ∃ e ∈ ambient ω,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (loss : ℝ)
    (hbudget :
      (Fintype.card State : ℝ) * loss +
          ∑ ω, ((((target ω) ×ˢ (ambient ω)).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              vertex i p.1 = vertex i p.2)).card : ℝ) ≤
        ∑ ω, ((target ω).card : ℝ)) :
    ∃ ω : State, ∃ kept : Finset Edge,
      kept ⊆ target ω ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ vertex i e.1)) ∧
      (∀ x y z : kept,
        supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
      loss ≤ (kept.card : ℝ) := by
  classical
  let collisions : State → Finset (Edge × Edge) := fun ω ↦
    ((target ω) ×ˢ (ambient ω)).filter (fun p ↦
      p.1 ≠ p.2 ∧ ∃ i : Fin 3, vertex i p.1 = vertex i p.2)
  let good : State → ℕ := fun ω ↦ (target ω).card
  let bad : State → ℕ := fun ω ↦ (collisions ω).card
  have hbudget' :
      (Fintype.card State : ℝ) * loss + ∑ ω, (bad ω : ℝ) ≤
        ∑ ω, (good ω : ℝ) := by
    simpa only [bad, good, collisions] using hbudget
  obtain ⟨ω, hω⟩ :=
    mme_finite_collision_budget_averaging_real good bad loss hbudget'
  obtain ⟨kept, hkept, hseparated, hisolated, hcard⟩ :=
    mme_tripartite_target_isolation_pruning
      vertex (ambient ω) (target ω) (htarget ω)
  have hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1) := by
    intro i x y hxy
    apply Subtype.ext
    by_contra hne
    exact hseparated x.1 x.2 y.1 y.2 hne i hxy
  have hinduced : ∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z := by
    intro x y z hsupp
    obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
      hclosure ω x.1 (hkept x.2) y.1 (hkept y.2) z.1 (hkept z.2) hsupp
    have heKept : e ∈ kept := hisolated e heAmbient (by
      intro i
      fin_cases i
      · exact ⟨x.1, x.2, he0⟩
      · exact ⟨y.1, y.2, he1⟩
      · exact ⟨z.1, z.2, he2⟩)
    let e' : kept := ⟨e, heKept⟩
    have hex : e' = x := hmode 0 he0
    have hey : e' = y := hmode 1 he1
    have hez : e' = z := hmode 2 he2
    exact ⟨hex.symm.trans hey, hey.symm.trans hez⟩
  refine ⟨ω, kept, hkept, hmode, hinduced, ?_⟩
  have hcardReal : ((target ω).card : ℝ) ≤
      (kept.card : ℝ) + (collisions ω).card := by
    exact_mod_cast hcard
  have hω' : ((collisions ω).card : ℝ) + loss ≤
      ((target ω).card : ℝ) := by
    simpa only [bad, good] using hω
  linarith
