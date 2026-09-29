-- Prove2me | solution 1 for mme_stothers_phi233_actual_degree_half_margin_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-04T05:43:02.5783+00:00
-- url     : https://prove2.me/submissions/d23688d7-3c08-4f22-987a-d6c25d085bff

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_hash_state_card
import Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
import Theorems.Thm_mme_stothers_phi233_named_hash_fiber_package
import Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option warningAsError true

/-- The direct finite Phi233 extraction in terms of its actual ambient cyclic
mode degree.  This is the form matched by the existing bounded-degree
prime/Behrend theorem. -/
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
  letI : Nonempty (HashState p N) :=
    ⟨((fun _ ↦ 0), 0)⟩
  obtain ⟨hedge, hpair⟩ :=
    mme_stothers_phi233_named_hash_fiber_package
      (p := p) (N := N) (alpha := alpha) (beta := beta)
      (gamma := gamma) (delta := delta) hp S
  have hclosure : ∀ q : HashState p N,
      ∀ x ∈ (targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S q),
      ∀ y ∈ (targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S q),
      ∀ z ∈ (targetFinset N alpha beta gamma delta).filter
        (Retained p N alpha beta gamma delta S q),
        CyclicCoordinatewiseSupported x y z →
          ∃ e ∈ (ambientFinset N alpha beta gamma delta).filter
            (Retained p N alpha beta gamma delta S q),
            cyclicModeWord e 0 = cyclicModeWord x 0 ∧
            cyclicModeWord e 1 = cyclicModeWord y 1 ∧
            cyclicModeWord e 2 = cyclicModeWord z 2 := by
    intro q x hx y hy z hz hsupp
    have hx' : x ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa only [retainedTarget] using hx
    have hy' : y ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa only [retainedTarget] using hy
    have hz' : z ∈ retainedTarget p N alpha beta gamma delta S q := by
      simpa only [retainedTarget] using hz
    obtain ⟨e, he, he0, he1, he2⟩ :=
      mme_stothers_phi233_retained_target_ambient_closure
        S hSfree q x hx' y hy' z hz' hsupp
    exact ⟨e, by simpa only [retainedAmbient] using he, he0, he1, he2⟩
  have htargetAmbient : targetFinset N alpha beta gamma delta ⊆
      ambientFinset N alpha beta gamma delta :=
    (mme_stothers_phi233_cyclic_finset_cardinalities
      N alpha beta gamma delta).1
  let frac : ℝ :=
    (S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))
  let loss : ℝ := (Dstar : ℝ) * frac
  have hp2 : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by
    positivity
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
  obtain ⟨q, kept, hkept, hinj, hdiag, hcard⟩ :=
    mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      (State := HashState p N)
      (Edge := CyclicAmbientEdge N alpha beta gamma delta)
      (Vertex := fun _ ↦ CyclicModeWord N)
      (fun i e ↦ cyclicModeWord e i)
      CyclicCoordinatewiseSupported
      (ambientFinset N alpha beta gamma delta)
      (targetFinset N alpha beta gamma delta)
      (Retained p N alpha beta gamma delta S)
      (p ^ 2) S.card (p ^ (6 * N)) D Dstar
      (V : ℝ) loss
      (Nat.cast_nonneg V) hstate htargetCard hdegree hedge hpair
      htargetAmbient hclosure hmargin
  refine ⟨q, kept, by simpa only [retainedTarget] using hkept,
    hinj, hdiag, ?_⟩
  calc
    ((targetFinset N alpha beta gamma delta).card : ℝ) *
        ((S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))) =
        (V : ℝ) * loss := by
          rw [htargetCard]
          dsimp only [loss, frac]
          ring
    _ ≤ (kept.card : ℝ) := hcard
