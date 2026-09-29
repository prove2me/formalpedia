-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.perfect_hvzk
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T10:21:35.600587+00:00
-- url     : https://prove2.me/submissions/71bbf850-9ea1-4bf9-b61b-e3d5430e7cbc

/-
# `MachineLearning.CommittedLocalOracleZK.perfect_hvzk`
Target `4951ccec` (Open; re-read live immediately before submitting).

ORDINARY PROOF - screen CLEAN. Gift: **SAFE** (live-checked).

BINDERS - from this target's own WA, verbatim: ELEVEN instances, adding `[Nonempty S]` to
`60d95eb7`'s list. `Pr` and `sim` IMPLICIT; `hH`, `hS`, `tau` explicit.

MATHS. `realProb = realCount / (|P| * |Rc| * |Rv|)` and `simProb = simCount / (|S| * |Rc| * |Rv|)`,
both in Q. Cross-multiplying `realCount * |S| = simCount * |P|` (proved inline below, as
`realCount_mul_card_sim`) gives the claim.

THE DEGENERATE CASE IS REAL, not bookkeeping. If `|Rc| * |Rv| = 0` then BOTH denominators are zero,
and Lean's `x / 0 = 0` makes both sides `0` - so the equality holds, but NOT by the division argument,
which would be invalid. It is split off explicitly. In the main case `|P| > 0` and `|S| > 0` come from
`[Nonempty P]` and `[Nonempty S]`, which is exactly why this target carries one more instance than
`60d95eb7`: the extra `Nonempty S` is load-bearing.

`realCount_mul_card_sim` (with `realCount_eq_sum`, `simCount_eq_sum`, `fiberCount_congr` inside it) is
RE-DERIVED INLINE below - importing from `Theorems/` would force the reduction path and an axiom
audit. That is why this file is long; the mathematics is entirely mechanical.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MachineLearning.CommittedLocalOracleZK Finset

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A C O Rc Rv P S : Type*} [DecidableEq I] [Fintype I] [Fintype Rc] [Fintype Rv]
    [Fintype P] [Fintype S] [DecidableEq A] [DecidableEq C] [DecidableEq O] [DecidableEq Rv]
    [Nonempty P] [Nonempty S] {Pr : CommittedOracle I A C O Rc Rv P} {sim : Rv → S → I → A}
    (hH : PerfectlyHidesUnopened Pr) (hS : PerfectlySimulatesOpened Pr sim)
    (τ : Transcript I A C O Rv) :
    realProb Pr τ = simProb Pr sim τ := by
  classical
  obtain ⟨c, r₀, t, o⟩ := τ
  have hmul : realCount Pr (c, r₀, t, o) * Fintype.card S
      = simCount Pr sim (c, r₀, t, o) * Fintype.card P := by
    -- (0) a restriction equality gives pointwise agreement ON the queried set
    have hagree : ∀ (T : Finset I) (u v : I → A),
        restrictTo T u = restrictTo T v → ∀ i ∈ T, u i = v i := by
      intro T u v hres i hi
      have := congrFun hres i
      simp only [restrictTo, if_pos hi] at this
      exact Option.some_injective _ this
    -- (1) fiberCount_congr, re-derived inline
    have hfib : ∀ (T : Finset I) (u v : I → A), (∀ i ∈ T, u i = v i) →
        ∀ (cc : C) (oo : O), fiberCount Pr u T cc oo = fiberCount Pr v T cc oo := by
      intro T u v huv cc oo
      obtain ⟨e, he⟩ := hH T u v huv
      show (Finset.univ.filter fun ρ => Pr.com u ρ = cc ∧ Pr.openInfo u ρ T = oo).card
          = (Finset.univ.filter fun ρ => Pr.com v ρ = cc ∧ Pr.openInfo v ρ T = oo).card
      refine Finset.card_equiv e ?_
      intro ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(he ρ).1, (he ρ).2]
    -- (2) realCount_eq_sum, re-derived inline
    have hreal : realCount Pr (c, r₀, t, o)
        = ∑ p, if restrictTo (Pr.Q r₀) (Pr.proof p) = t
               then fiberCount Pr (Pr.proof p) (Pr.Q r₀) c o else 0 := by
      show (Finset.univ.filter fun x : P × Rc × Rv =>
              realTranscript Pr x.1 x.2.1 x.2.2 = (c, r₀, t, o)).card = _
      rw [Finset.card_eq_sum_card_fiberwise
            (f := fun x : P × Rc × Rv => x.1) (t := (Finset.univ : Finset P))
            (fun x _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl ?_
      intro p _
      have hmem : ∀ x : P × Rc × Rv,
          (x ∈ (Finset.univ.filter fun y : P × Rc × Rv =>
                  realTranscript Pr y.1 y.2.1 y.2.2 = (c, r₀, t, o)).filter (fun y => y.1 = p))
            ↔ (x.1 = p ∧ x.2.2 = r₀ ∧ restrictTo (Pr.Q r₀) (Pr.proof p) = t ∧
                Pr.com (Pr.proof p) x.2.1 = c ∧ Pr.openInfo (Pr.proof p) x.2.1 (Pr.Q r₀) = o) := by
        intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, realTranscript, Prod.mk_inj]
        constructor
        · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
          subst h5; subst h2
          exact ⟨rfl, rfl, h3, h1, h4⟩
        · rintro ⟨h5, h2, h3, h1, h4⟩
          subst h5; subst h2
          exact ⟨⟨h1, rfl, h3, h4⟩, rfl⟩
      by_cases hrest : restrictTo (Pr.Q r₀) (Pr.proof p) = t
      · rw [if_pos hrest]
        show _ = (Finset.univ.filter fun ρ =>
                    Pr.com (Pr.proof p) ρ = c ∧ Pr.openInfo (Pr.proof p) ρ (Pr.Q r₀) = o).card
        refine Finset.card_nbij' (fun x => x.2.1) (fun ρ => (p, ρ, r₀)) ?_ ?_ ?_ ?_
        · intro x hx
          rw [Finset.mem_coe, hmem] at hx
          simpa using ⟨hx.2.2.2.1, hx.2.2.2.2⟩
        · intro ρ hρ
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hρ
          rw [Finset.mem_coe, hmem]
          exact ⟨rfl, rfl, hrest, hρ.1, hρ.2⟩
        · intro x hx
          rw [Finset.mem_coe, hmem] at hx
          obtain ⟨h1, h2, -, -, -⟩ := hx
          exact Prod.ext h1.symm (Prod.ext rfl h2.symm)
        · intro ρ _
          rfl
      · rw [if_neg hrest, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        intro hx1
        apply hrest
        have hcopy := hx
        simp only [realTranscript, Prod.mk_inj] at hcopy
        obtain ⟨-, h2, h3, -⟩ := hcopy
        subst hx1
        rw [← h2]
        exact h3
    -- (3) simCount_eq_sum, re-derived inline (the mirror)
    have hsimc : simCount Pr sim (c, r₀, t, o)
        = ∑ s, if restrictTo (Pr.Q r₀) (sim r₀ s) = t
               then fiberCount Pr (sim r₀ s) (Pr.Q r₀) c o else 0 := by
      show (Finset.univ.filter fun x : S × Rc × Rv =>
              simTranscript Pr sim x.1 x.2.1 x.2.2 = (c, r₀, t, o)).card = _
      rw [Finset.card_eq_sum_card_fiberwise
            (f := fun x : S × Rc × Rv => x.1) (t := (Finset.univ : Finset S))
            (fun x _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl ?_
      intro s _
      have hmem : ∀ x : S × Rc × Rv,
          (x ∈ (Finset.univ.filter fun y : S × Rc × Rv =>
                  simTranscript Pr sim y.1 y.2.1 y.2.2 = (c, r₀, t, o)).filter (fun y => y.1 = s))
            ↔ (x.1 = s ∧ x.2.2 = r₀ ∧ restrictTo (Pr.Q r₀) (sim r₀ s) = t ∧
                Pr.com (sim r₀ s) x.2.1 = c ∧ Pr.openInfo (sim r₀ s) x.2.1 (Pr.Q r₀) = o) := by
        intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, simTranscript, Prod.mk_inj]
        constructor
        · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
          subst h5; subst h2
          exact ⟨rfl, rfl, h3, h1, h4⟩
        · rintro ⟨h5, h2, h3, h1, h4⟩
          subst h5; subst h2
          exact ⟨⟨h1, rfl, h3, h4⟩, rfl⟩
      by_cases hrest : restrictTo (Pr.Q r₀) (sim r₀ s) = t
      · rw [if_pos hrest]
        show _ = (Finset.univ.filter fun ρ =>
                    Pr.com (sim r₀ s) ρ = c ∧ Pr.openInfo (sim r₀ s) ρ (Pr.Q r₀) = o).card
        refine Finset.card_nbij' (fun x => x.2.1) (fun ρ => (s, ρ, r₀)) ?_ ?_ ?_ ?_
        · intro x hx
          rw [Finset.mem_coe, hmem] at hx
          simpa using ⟨hx.2.2.2.1, hx.2.2.2.2⟩
        · intro ρ hρ
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hρ
          rw [Finset.mem_coe, hmem]
          exact ⟨rfl, rfl, hrest, hρ.1, hρ.2⟩
        · intro x hx
          rw [Finset.mem_coe, hmem] at hx
          obtain ⟨h1, h2, -, -, -⟩ := hx
          exact Prod.ext h1.symm (Prod.ext rfl h2.symm)
        · intro ρ _
          rfl
      · rw [if_neg hrest, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        intro hx1
        apply hrest
        have hcopy := hx
        simp only [simTranscript, Prod.mk_inj] at hcopy
        obtain ⟨-, h2, h3, -⟩ := hcopy
        subst hx1
        rw [← h2]
        exact h3
    -- (4) collapse each sum to (count of survivors) * F
    set FP := Finset.univ.filter fun p : P => restrictTo (Pr.Q r₀) (Pr.proof p) = t with hFP
    set FS := Finset.univ.filter fun s : S => restrictTo (Pr.Q r₀) (sim r₀ s) = t with hFS
    have hsumP : ∀ F : ℕ, (∀ p ∈ FP, fiberCount Pr (Pr.proof p) (Pr.Q r₀) c o = F) →
        (∑ p, if restrictTo (Pr.Q r₀) (Pr.proof p) = t
              then fiberCount Pr (Pr.proof p) (Pr.Q r₀) c o else 0) = FP.card * F := by
      intro F hF
      rw [← Finset.sum_filter, ← hFP, Finset.sum_congr rfl hF, Finset.sum_const, smul_eq_mul]
    have hsumS : ∀ F : ℕ, (∀ s ∈ FS, fiberCount Pr (sim r₀ s) (Pr.Q r₀) c o = F) →
        (∑ s, if restrictTo (Pr.Q r₀) (sim r₀ s) = t
              then fiberCount Pr (sim r₀ s) (Pr.Q r₀) c o else 0) = FS.card * F := by
      intro F hF
      rw [← Finset.sum_filter, ← hFS, Finset.sum_congr rfl hF, Finset.sum_const, smul_eq_mul]
    -- (5) the two cases
    rcases Finset.eq_empty_or_nonempty FP with hemp | ⟨p₀, hp₀⟩
    · -- no surviving prover randomness: both counts vanish, using Nonempty P
      have hr0 : realCount Pr (c, r₀, t, o) = 0 := by
        rw [hreal, ← Finset.sum_filter, ← hFP, hemp, Finset.sum_empty]
      have hcardP : 0 < Fintype.card P := Fintype.card_pos
      have hkey := hS r₀ t
      rw [← hFP, ← hFS, hemp] at hkey
      simp only [Finset.card_empty, zero_mul] at hkey
      have hFS0 : FS.card = 0 := by
        rcases Nat.eq_zero_or_pos FS.card with h | h
        · exact h
        · exact absurd hkey.symm (Nat.ne_of_gt (Nat.mul_pos h hcardP))
      have hs0 : simCount Pr sim (c, r₀, t, o) = 0 := by
        rw [hsimc, ← Finset.sum_filter, ← hFS, Finset.card_eq_zero.mp hFS0, Finset.sum_empty]
      rw [hr0, hs0, zero_mul, zero_mul]
    · -- a survivor exists: every surviving fiberCount equals the one at p₀
      set F := fiberCount Pr (Pr.proof p₀) (Pr.Q r₀) c o with hFdef
      have hp₀t : restrictTo (Pr.Q r₀) (Pr.proof p₀) = t := (Finset.mem_filter.mp hp₀).2
      have hFP' : ∀ p ∈ FP, fiberCount Pr (Pr.proof p) (Pr.Q r₀) c o = F := by
        intro p hp
        have hpt : restrictTo (Pr.Q r₀) (Pr.proof p) = t := (Finset.mem_filter.mp hp).2
        exact hfib _ _ _ (hagree _ _ _ (hpt.trans hp₀t.symm)) c o
      have hFS' : ∀ s ∈ FS, fiberCount Pr (sim r₀ s) (Pr.Q r₀) c o = F := by
        intro s hs
        have hst : restrictTo (Pr.Q r₀) (sim r₀ s) = t := (Finset.mem_filter.mp hs).2
        exact hfib _ _ _ (hagree _ _ _ (hst.trans hp₀t.symm)) c o
      rw [hreal, hsumP F hFP', hsimc, hsumS F hFS']
      have hkey := hS r₀ t
      rw [← hFP, ← hFS] at hkey
      calc FP.card * F * Fintype.card S = FP.card * Fintype.card S * F := by ring
        _ = FS.card * Fintype.card P * F := by rw [hkey]
        _ = FS.card * F * Fintype.card P := by ring
  -- cross-multiply in Q
  show (realCount Pr (c, r₀, t, o) : ℚ) / (Fintype.card P * Fintype.card Rc * Fintype.card Rv)
      = (simCount Pr sim (c, r₀, t, o) : ℚ) / (Fintype.card S * Fintype.card Rc * Fintype.card Rv)
  have hmulQ : (realCount Pr (c, r₀, t, o) : ℚ) * (Fintype.card S : ℚ)
      = (simCount Pr sim (c, r₀, t, o) : ℚ) * (Fintype.card P : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hmul
  by_cases hz : (Fintype.card Rc : ℚ) * (Fintype.card Rv : ℚ) = 0
  · -- both denominators vanish; Lean's x / 0 = 0 makes both sides 0
    have h1 : (Fintype.card P : ℚ) * Fintype.card Rc * Fintype.card Rv = 0 := by
      rw [mul_assoc]; rw [hz]; ring
    have h2 : (Fintype.card S : ℚ) * Fintype.card Rc * Fintype.card Rv = 0 := by
      rw [mul_assoc]; rw [hz]; ring
    rw [h1, h2, div_zero, div_zero]
  · have hP : (Fintype.card P : ℚ) ≠ 0 := by
      have : 0 < Fintype.card P := Fintype.card_pos
      positivity
    have hSc : (Fintype.card S : ℚ) ≠ 0 := by
      have : 0 < Fintype.card S := Fintype.card_pos
      positivity
    rw [div_eq_div_iff (by simpa [mul_assoc] using mul_ne_zero hP hz)
                       (by simpa [mul_assoc] using mul_ne_zero hSc hz)]
    calc (realCount Pr (c, r₀, t, o) : ℚ) * (Fintype.card S * Fintype.card Rc * Fintype.card Rv)
        = ((realCount Pr (c, r₀, t, o) : ℚ) * Fintype.card S)
            * (Fintype.card Rc * Fintype.card Rv) := by ring
      _ = ((simCount Pr sim (c, r₀, t, o) : ℚ) * Fintype.card P)
            * (Fintype.card Rc * Fintype.card Rv) := by rw [hmulQ]
      _ = (simCount Pr sim (c, r₀, t, o) : ℚ)
            * (Fintype.card P * Fintype.card Rc * Fintype.card Rv) := by ring
