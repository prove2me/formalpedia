-- Prove2me | solution 1 for mme_stothers_phi233_concrete_fractional_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:27:54.096815+00:00
-- url     : https://prove2.me/submissions/006731c2-1443-4551-b1cc-5c3ceca44bb9

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_hash_state_card
import Theorems.Thm_mme_stothers_phi233_cyclic_relative_degree_package
import Theorems.Thm_mme_stothers_phi233_named_hash_fiber_package
import Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
import Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option warningAsError true

/-- The Phi233 affine hash and the relative completion-degree estimate give a
concrete large isolated cyclic target family under the normalized finite
margin. -/
theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : ExactProfileAddress N alpha beta gamma delta)
    (S : Finset (ZMod p))
    (hSfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x + y = 2 * z → x = z ∧ z = y)
    (R ell : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card (MarginalAddress N alpha beta gamma delta) : ℝ) ≤
        R * (Nat.card
          (ExactProfileAddress N alpha beta gamma delta) : ℝ))
    (hmargin :
      ((p ^ 2 : ℕ) : ℝ) * ell +
          3 * R ^ 3 *
            ((∏ l : Fin 3,
              Nat.card
                {b : ExactProfileAddress N alpha beta gamma delta //
                  b.1.1 l = a.1.1 l}) : ℝ) ≤
        (S.card : ℝ)) :
    ∃ q : HashState p N,
      ∃ kept : Finset (CyclicAmbientEdge N alpha beta gamma delta),
        kept ⊆ retainedTarget p N alpha beta gamma delta S q ∧
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        ((targetFinset N alpha beta gamma delta).card : ℝ) * ell ≤
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
  have hpackage := mme_stothers_phi233_cyclic_relative_degree_package
    N alpha beta gamma delta hsum a R hR hratio
  change
    (∀ i : Fin 3, ∀ e ∈ targetFinset N alpha beta gamma delta,
      ((ambientFinset N alpha beta gamma delta).filter
        (fun b ↦ cyclicModeWord b i = cyclicModeWord e i)).card ≤ D) ∧
    (∀ i : Fin 3, ∀ e ∈ targetFinset N alpha beta gamma delta,
      ((targetFinset N alpha beta gamma delta).filter
        (fun b ↦ cyclicModeWord b i = cyclicModeWord e i)).card = Dstar) ∧
    ((targetFinset N alpha beta gamma delta).card : ℝ) =
      (V : ℝ) * (Dstar : ℝ) ∧
    (D : ℝ) ≤ R ^ 3 * (Dstar : ℝ) at hpackage
  rcases hpackage with ⟨hdegree, htargetDegree, htargetCard, hdegreeRatio⟩
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
  have hmargin' :
      ((p ^ 2 : ℕ) : ℝ) * ell +
          3 * (R ^ 3) * (Dstar : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Dstar, Nat.cast_prod] using hmargin
  obtain ⟨q, kept, hkept, hinj, hdiag, hcard⟩ :=
    mme_type2_fractional_retention_of_relative_mode_degree
      (State := HashState p N)
      (Edge := CyclicAmbientEdge N alpha beta gamma delta)
      (Vertex := fun _ ↦ CyclicModeWord N)
      (fun i e ↦ cyclicModeWord e i)
      CyclicCoordinatewiseSupported
      (ambientFinset N alpha beta gamma delta)
      (targetFinset N alpha beta gamma delta)
      (Retained p N alpha beta gamma delta S)
      (p ^ 2) S.card (p ^ (6 * N)) D Dstar
      (V : ℝ) (R ^ 3) ell
      (Nat.cast_nonneg V) hstate htargetCard hdegree hdegreeRatio
      hedge hpair htargetAmbient hclosure hmargin'
  exact ⟨q, kept, by simpa only [retainedTarget] using hkept,
    hinj, hdiag, hcard⟩
