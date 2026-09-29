-- Prove2me | solution 1 for mme_stothers_phi134_finite_isolation_of_hash_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:47:00.866903+00:00
-- url     : https://prove2.me/submissions/2a19fa87-bb14-4156-a5d5-63769be4c4f8

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi134_capacity_identity
import Theorems.Thm_mme_stothers_phi134_hash_degree_bound
import Theorems.Thm_mme_stothers_phi134_cyclic_edge_retention_card
import Theorems.Thm_mme_stothers_phi134_cyclic_pair_retention_card_le
import Theorems.Thm_mme_stothers_phi134_retained_exact_closure
import Theorems.Thm_mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- The source-specific finite Type-2 isolation adapter for `Phi134`.
The only remaining quantitative input is the collision margin. -/
theorem solution
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : alpha + beta + gamma + delta = N)
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (loss : ℝ) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let State := (I → ZMod p) × ZMod p
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : State) (i : Fin 3)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    let retain := fun (q : State)
        (e : CyclicExactEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    let Dstar := D 0 * (D 1 * D 2)
    let V := ∏ i : Fin 3,
      Nat.multinomial Finset.univ
        (marginalMultiplicity N alpha beta gamma delta i)
    ((p ^ 2 : ℕ) : ℝ) * loss +
          3 * (Dstar : ℝ) * (Dstar : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) →
      ∃ q : State,
        ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
          kept ⊆ (edgeFinset N alpha beta gamma delta).filter (retain q) ∧
          (∀ i : Fin 3,
            Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
          (∀ x y z : kept,
            CyclicCoordinatewiseSupported x.1 y.1 z.1 →
              x = y ∧ y = z) ∧
          (V : ℝ) * loss ≤ (kept.card : ℝ) := by
  classical
  dsimp only
  let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
  let State := (I → ZMod p) × ZMod p
  let weights := fun w : I → ZMod p ↦
    fun r j ↦ w (Sum.inl (r, j))
  let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
  let H := fun (q : State) (i : Fin 3)
      (e : CyclicExactEdge N alpha beta gamma delta) ↦
    cyclicAffineHash p N alpha beta gamma delta
      (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
  let retain := fun (q : State)
      (e : CyclicExactEdge N alpha beta gamma delta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
  let D : Fin 3 → ℕ := fun t ↦
    ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial
  let Dstar : ℕ := D 0 * (D 1 * D 2)
  let V : ℕ := ∏ i : Fin 3,
    Nat.multinomial Finset.univ
      (marginalMultiplicity N alpha beta gamma delta i)
  intro hmargin
  change ((p ^ 2 : ℕ) : ℝ) * loss +
      3 * (Dstar : ℝ) * (Dstar : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ) at hmargin
  change ∃ q : State,
    ∃ kept : Finset (CyclicExactEdge N alpha beta gamma delta),
      kept ⊆ (edgeFinset N alpha beta gamma delta).filter (retain q) ∧
      (∀ i : Fin 3,
        Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
      (∀ x y z : kept,
        CyclicCoordinatewiseSupported x.1 y.1 z.1 →
          x = y ∧ y = z) ∧
      (V : ℝ) * loss ≤ (kept.card : ℝ)
  letI : Nonempty State := ⟨((fun _ ↦ 0), 0)⟩
  have hstate : Fintype.card State = p ^ 2 * p ^ (6 * N) := by
    dsimp only [State, I]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit, ZMod.card]
    rw [show 3 * (2 * N) + 1 = 6 * N + 1 by omega]
    ring
  have hedgeCardNat :
      (edgeFinset N alpha beta gamma delta).card =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
    letI := exactProfileAddressFintype N alpha beta gamma delta
    letI := cyclicExactEdgeFintype N alpha beta gamma delta
    change Fintype.card
        (ExactProfileAddress N alpha beta gamma delta ×
          (ExactProfileAddress N alpha beta gamma delta ×
            ExactProfileAddress N alpha beta gamma delta)) = _
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_prod]
    ring
  have hcapacity := mme_stothers_phi134_capacity_identity
    N alpha beta gamma delta hsum
  change V * Dstar =
    (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hcapacity
  have htargetCard :
      ((edgeFinset N alpha beta gamma delta).card : ℝ) =
        (V : ℝ) * (Dstar : ℝ) := by
    exact_mod_cast hedgeCardNat.trans hcapacity.symm
  have hdegree : ∀ i : Fin 3,
      ∀ e ∈ edgeFinset N alpha beta gamma delta,
        ((edgeFinset N alpha beta gamma delta).filter
          (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤
            Dstar := by
    simpa only [D, Dstar] using
      (mme_stothers_phi134_hash_degree_bound
        N alpha beta gamma delta hsum)
  have hedge : ∀ e ∈ edgeFinset N alpha beta gamma delta,
      ((Finset.univ : Finset State).filter
        (fun q ↦ retain q e)).card =
          S.card * p ^ (6 * N) := by
    intro e _he
    simpa only [State, retain, H, I, weights, shift] using
      (mme_stothers_phi134_cyclic_edge_retention_card hp e S)
  have hpair : ∀ ef ∈
      ((edgeFinset N alpha beta gamma delta ×ˢ
        edgeFinset N alpha beta gamma delta).filter (fun ef ↦
          ef.1 ≠ ef.2 ∧ ∃ i : Fin 3,
            cyclicModeWord ef.1 i = cyclicModeWord ef.2 i)),
      ((Finset.univ : Finset State).filter (fun q ↦
        retain q ef.1 ∧ retain q ef.2)).card ≤
        p ^ (6 * N) := by
    intro ef hef
    simp only [Finset.mem_filter, Finset.mem_product] at hef
    obtain ⟨hne, i, hi⟩ := hef.2
    simpa only [State, retain, H, I, weights, shift] using
      (mme_stothers_phi134_cyclic_pair_retention_card_le
        hp ef.1 ef.2 S hne i hi)
  have hclosure : ∀ q : State,
      ∀ x ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
      ∀ y ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
      ∀ z ∈ (edgeFinset N alpha beta gamma delta).filter
        (retain q),
        CyclicCoordinatewiseSupported x y z →
          ∃ e ∈ (edgeFinset N alpha beta gamma delta).filter
            (retain q),
            cyclicModeWord e 0 = cyclicModeWord x 0 ∧
            cyclicModeWord e 1 = cyclicModeWord y 1 ∧
            cyclicModeWord e 2 = cyclicModeWord z 2 := by
    intro q x hx y hy z hz hsupp
    have hx' : x ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, stateWeights, stateShift, weights, shift] using hx
    have hy' : y ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, stateWeights, stateShift, weights, shift] using hy
    have hz' : z ∈ retainedEdges p N alpha beta gamma delta S q := by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, stateWeights, stateShift, weights, shift] using hz
    obtain ⟨e, he, he0, he1, he2⟩ :=
      mme_stothers_phi134_retained_exact_closure
        S hSfree q x hx' y hy' z hz' hsupp
    exact ⟨e, by
      simpa only [retainedEdges, Finset.mem_filter, retain, H, State, I,
        Retained, stateHash, stateWeights, stateShift, weights, shift] using he,
      he0, he1, he2⟩
  exact
    (mme_type2_sharp_retained_cardinality_of_uniform_hash_fibers
      (Vertex := fun _ ↦ CyclicModeWord N)
      (fun i e ↦ cyclicModeWord e i)
      CyclicCoordinatewiseSupported
      (edgeFinset N alpha beta gamma delta)
      (edgeFinset N alpha beta gamma delta)
      retain
      (p ^ 2) S.card (p ^ (6 * N)) Dstar Dstar
      (V : ℝ) loss (Nat.cast_nonneg V) hstate htargetCard hdegree
      hedge hpair Finset.Subset.rfl hclosure hmargin)
