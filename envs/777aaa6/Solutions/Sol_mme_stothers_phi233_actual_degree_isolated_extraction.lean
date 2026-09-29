-- Prove2me | solution 1 for mme_stothers_phi233_actual_degree_isolated_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T05:38:16.306277+00:00
-- url     : https://prove2.me/submissions/10abf0f8-79c5-409e-940d-7c2e0e9c3286

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_hash_state_card
import Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
import Theorems.Thm_mme_stothers_phi233_named_hash_fiber_package
import Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
import Theorems.Thm_mme_type2_uniform_hash_retention_aggregate_incidence
import Theorems.Thm_mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
import Theorems.Thm_mme_finite_collision_budget_averaging_real
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option warningAsError true

/-- Actual-degree half-margin extraction that also exports ambient isolation.
This is the form required by `isolated_kept_profile_value`. -/
theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : ExactProfileAddress N alpha beta gamma delta)
    (S : Finset (ZMod p))
    (hSfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x + y = 2 * z → x = z ∧ z = y)
    (hlarge :
      6 *
          ((∏ l : Fin 3,
            Nat.card
              {b : MarginalAddress N alpha beta gamma delta //
                b.1 l = a.1.1 l}) : ℝ) ≤
        (S.card : ℝ)) :
    ∃ q : HashState p N,
      ∃ kept : Finset (CyclicAmbientEdge N alpha beta gamma delta),
        kept ⊆ retainedTarget p N alpha beta gamma delta S q ∧
        (∀ e ∈ retainedAmbient p N alpha beta gamma delta S q,
          (∀ i : Fin 3, ∃ f ∈ kept,
            cyclicModeWord e i = cyclicModeWord f i) →
          e ∈ kept) ∧
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        ((targetFinset N alpha beta gamma delta).card : ℝ) *
            ((S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))) ≤
          (kept.card : ℝ) := by
  classical
  let D : ℕ := ∏ l : Fin 3,
    Nat.card
      {b : MarginalAddress N alpha beta gamma delta //
        b.1 l = a.1.1 l}
  let Dstar : ℕ := ∏ l : Fin 3,
    Nat.card
      {b : ExactProfileAddress N alpha beta gamma delta //
        b.1.1 l = a.1.1 l}
  let V : ℕ := ∏ l : Fin 3,
    ((2 * N).factorial /
      ∏ s : Fin 5,
        (marginalMultiplicity alpha beta gamma delta l s).factorial)
  have hdegrees := mme_stothers_phi233_uniform_cyclic_mode_degrees
    N alpha beta gamma delta hsum a
  change
    (∀ i : Fin 3, ∀ e ∈ targetFinset N alpha beta gamma delta,
      ((ambientFinset N alpha beta gamma delta).filter
        (fun b ↦ cyclicModeWord b i = cyclicModeWord e i)).card = D) ∧
    (∀ i : Fin 3, ∀ e ∈ targetFinset N alpha beta gamma delta,
      ((targetFinset N alpha beta gamma delta).filter
        (fun b ↦ cyclicModeWord b i = cyclicModeWord e i)).card = Dstar) ∧
    (targetFinset N alpha beta gamma delta).card = V * Dstar at hdegrees
  rcases hdegrees with ⟨hdegreeEq, _htargetDegree, htargetCardNat⟩
  have hdegree : ∀ i : Fin 3, ∀ e ∈
      targetFinset N alpha beta gamma delta,
      ((ambientFinset N alpha beta gamma delta).filter
        (fun b ↦ cyclicModeWord b i = cyclicModeWord e i)).card ≤ D := by
    intro i e he
    exact (hdegreeEq i e he).le
  have htargetCard :
      ((targetFinset N alpha beta gamma delta).card : ℝ) =
        (V : ℝ) * (Dstar : ℝ) := by
    exact_mod_cast htargetCardNat
  have hstate : Fintype.card (HashState p N) =
      p ^ 2 * p ^ (6 * N) :=
    mme_stothers_phi233_hash_state_card p N
  letI : Nonempty (HashState p N) := ⟨((fun _ ↦ 0), 0)⟩
  obtain ⟨hedge, hpair⟩ :=
    mme_stothers_phi233_named_hash_fiber_package
      (p := p) (N := N) (alpha := alpha) (beta := beta)
      (gamma := gamma) (delta := delta) hp S
  have htargetAmbient : targetFinset N alpha beta gamma delta ⊆
      ambientFinset N alpha beta gamma delta :=
    (mme_stothers_phi233_cyclic_finset_cardinalities
      N alpha beta gamma delta).1
  let frac : ℝ := (S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))
  let loss : ℝ := (Dstar : ℝ) * frac
  have hp2 : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by positivity
  have hcancel :
      ((p ^ 2 : ℕ) : ℝ) * frac = (S.card : ℝ) / 2 := by
    dsimp only [frac]
    field_simp
  have hlarge' : 6 * (D : ℝ) ≤ (S.card : ℝ) := by
    simpa only [D, Nat.cast_prod] using hlarge
  have hcollision :
      (Dstar : ℝ) * (3 * (D : ℝ)) ≤
        (Dstar : ℝ) * ((S.card : ℝ) / 2) := by
    apply mul_le_mul_of_nonneg_left
    · nlinarith
    · positivity
  have hmargin :
      ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) := by
    calc
      ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (Dstar : ℝ) * (D : ℝ) =
          (Dstar : ℝ) * (((p ^ 2 : ℕ) : ℝ) * frac) +
            (Dstar : ℝ) * (3 * (D : ℝ)) := by
              dsimp only [loss]
              ring
      _ = (Dstar : ℝ) * ((S.card : ℝ) / 2) +
            (Dstar : ℝ) * (3 * (D : ℝ)) := by rw [hcancel]
      _ ≤ (Dstar : ℝ) * ((S.card : ℝ) / 2) +
            (Dstar : ℝ) * ((S.card : ℝ) / 2) :=
        add_le_add_right hcollision _
      _ = (Dstar : ℝ) * (S.card : ℝ) := by ring
  obtain ⟨htargetInc, hcollInc⟩ :=
    mme_type2_uniform_hash_retention_aggregate_incidence
      (fun i e ↦ cyclicModeWord e i)
      (ambientFinset N alpha beta gamma delta)
      (targetFinset N alpha beta gamma delta)
      (Retained p N alpha beta gamma delta S)
      (S.card) (p ^ (6 * N)) hedge hpair
  have hbudget :=
    mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
      (fun i e ↦ cyclicModeWord e i)
      (ambientFinset N alpha beta gamma delta)
      (targetFinset N alpha beta gamma delta)
      (fun ω ↦ (ambientFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S ω))
      (fun ω ↦ (targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S ω))
      (p ^ 2) S.card (p ^ (6 * N)) D Dstar (V : ℝ) loss
      (Nat.cast_nonneg V) hstate htargetCard hdegree
      htargetInc hcollInc hmargin
  let good : HashState p N → ℕ := fun ω ↦
    ((targetFinset N alpha beta gamma delta).filter
      (Retained p N alpha beta gamma delta S ω)).card
  let bad : HashState p N → ℕ := fun ω ↦
    ((((targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S ω)) ×ˢ
      ((ambientFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S ω))).filter
      (fun p ↦
        p.1 ≠ p.2 ∧ ∃ i : Fin 3,
          cyclicModeWord p.1 i = cyclicModeWord p.2 i)).card
  have hbudget' :
      (Fintype.card (HashState p N) : ℝ) * ((V : ℝ) * loss) +
          ∑ ω, (bad ω : ℝ) ≤ ∑ ω, (good ω : ℝ) := by
    simpa [good, bad] using hbudget
  obtain ⟨q, hq⟩ :=
    mme_finite_collision_budget_averaging_real
      good bad ((V : ℝ) * loss) hbudget'
  let ambientRet := retainedAmbient p N alpha beta gamma delta S q
  let targetRet := retainedTarget p N alpha beta gamma delta S q
  have hTE : targetRet ⊆ ambientRet := by
    intro e he
    have he' : e ∈ (targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S q) := by
      simpa [targetRet, retainedTarget] using he
    have heT : e ∈ targetFinset N alpha beta gamma delta :=
      (Finset.mem_filter.mp he').1
    have heR : Retained p N alpha beta gamma delta S q e :=
      (Finset.mem_filter.mp he').2
    have heA : e ∈ ambientFinset N alpha beta gamma delta :=
      htargetAmbient heT
    simpa [ambientRet, retainedAmbient] using
      (Finset.mem_filter.mpr ⟨heA, heR⟩)
  obtain ⟨kept, hkept, hseparated, hisolated, hcard⟩ :=
    mme_tripartite_target_isolation_pruning
      (fun i e ↦ cyclicModeWord e i) ambientRet targetRet hTE
  have hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i) := by
    intro i x y hxy
    apply Subtype.ext
    by_contra hne
    exact hseparated x.1 x.2 y.1 y.2 hne i hxy
  have hclosure : ∀ x ∈ targetRet, ∀ y ∈ targetRet, ∀ z ∈ targetRet,
      CyclicCoordinatewiseSupported x y z →
        ∃ e ∈ ambientRet,
          cyclicModeWord e 0 = cyclicModeWord x 0 ∧
          cyclicModeWord e 1 = cyclicModeWord y 1 ∧
          cyclicModeWord e 2 = cyclicModeWord z 2 := by
    intro x hx y hy z hz hsupp
    have hx' : x ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa [targetRet] using hx
    have hy' : y ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa [targetRet] using hy
    have hz' : z ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa [targetRet] using hz
    obtain ⟨e, he, he0, he1, he2⟩ :=
      mme_stothers_phi233_retained_target_ambient_closure
        S hSfree q x hx' y hy' z hz' hsupp
    exact ⟨e, by simpa [ambientRet] using he, he0, he1, he2⟩
  have hdiag : ∀ x y z : kept,
      CyclicCoordinatewiseSupported x.1 y.1 z.1 →
        x = y ∧ y = z := by
    intro x y z hsupp
    obtain ⟨e, heAmbient, he0, he1, he2⟩ :=
      hclosure x.1 (hkept x.2) y.1 (hkept y.2) z.1 (hkept z.2) hsupp
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
  have hcardReal :
      ((targetRet).card : ℝ) ≤ (kept.card : ℝ) + (bad q : ℝ) := by
    have : targetRet.card ≤ kept.card +
        (((targetRet ×ˢ ambientRet).filter (fun p ↦
          p.1 ≠ p.2 ∧ ∃ i : Fin 3,
            cyclicModeWord p.1 i = cyclicModeWord p.2 i)).card) :=
      hcard
    simpa [bad, targetRet, ambientRet, retainedTarget, retainedAmbient] using
      (show (targetRet.card : ℝ) ≤ (kept.card : ℝ) +
          ((((targetRet ×ˢ ambientRet).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ i : Fin 3,
              cyclicModeWord p.1 i = cyclicModeWord p.2 i)).card : ℝ)) by
        exact_mod_cast this)
  have hq' : (bad q : ℝ) + (V : ℝ) * loss ≤ (good q : ℝ) := hq
  have hgood : (good q : ℝ) = (targetRet.card : ℝ) := by
    simp [good, targetRet, retainedTarget]
  refine ⟨q, kept, by simpa [targetRet, retainedTarget] using hkept,
    by
      intro e he hmodes
      have he' : e ∈ ambientRet := by simpa [ambientRet] using he
      exact hisolated e he' hmodes,
    hmode, hdiag, ?_⟩
  have hkeptLower : (V : ℝ) * loss ≤ (kept.card : ℝ) := by
    linarith [hcardReal, hq', hgood]
  calc
    ((targetFinset N alpha beta gamma delta).card : ℝ) *
        ((S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))) =
        (V : ℝ) * loss := by
          rw [htargetCard]
          dsimp only [loss, frac]
          ring
    _ ≤ (kept.card : ℝ) := hkeptLower
