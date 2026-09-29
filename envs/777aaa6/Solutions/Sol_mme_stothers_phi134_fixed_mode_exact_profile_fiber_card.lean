-- Prove2me | solution 1 for mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:53:09.849029+00:00
-- url     : https://prove2.me/submissions/f62c78a0-11b8-4177-a64b-296bd5cf8e93

import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem phi134_pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def phi134_addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem phi134_addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (phi134_addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem phi134_projectedFiberCard
    {N : ℕ} (g : Fin (2 * N) → Fin 8) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (g j) i = s)).card =
      ∑ r : {r : Fin 8 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ g j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // pattern (g j) i = s} ≃
        Sigma fun r : {r : Fin 8 // pattern r i = s} ↦
          {j : Fin (2 * N) // g j = r.1} := {
    toFun j := ⟨⟨g j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
      rw [x.2.2]
      exact x.1.2⟩
    left_inv j := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨r, hr⟩, ⟨j, hj⟩⟩
      cases hj
      rfl
  }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← Fintype.card_subtype]

private theorem phi134_sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (w : ExactProfileAddress N alpha beta gamma delta)
    (i : Fin 3) :
    Nat.card
        {v : ExactProfileAddress N alpha beta gamma delta //
          v.1.1 i = w.1.1 i} =
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial := by
  classical
  let multiplicity : Fin 8 → ℕ :=
    profileMultiplicity alpha beta gamma delta
  let Assignment :=
    {g : Fin (2 * N) → Fin 8 //
      (∀ j, pattern (g j) i = w.1.1 i j) ∧
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let Fiber :=
    {v : ExactProfileAddress N alpha beta gamma delta //
      v.1.1 i = w.1.1 i}
  have hprofileSum (l : Fin 3) (s : Fin 5) :
      (∑ r : {r : Fin 8 // pattern r l = s}, multiplicity r.1) =
        marginalMultiplicity N alpha beta gamma delta l s := by
    rw [← phi134_sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r l) s multiplicity]
    fin_cases l <;> fin_cases s <;>
      simp [multiplicity, pattern, profileMultiplicity,
        marginalMultiplicity, MME.cwSquareBlockType,
        Fin.sum_univ_succ] <;> omega
  let e : Fiber ≃ Assignment := {
    toFun v := ⟨fun j ↦ phi134_addressLabel v.1.1.1 v.1.1.2.1 j, by
      constructor
      · intro j
        have hj := congrFun
          (phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j) i
        exact hj.symm.trans (congrFun v.2 j)
      · intro r
        rw [Fintype.card_subtype]
        change _ = profileMultiplicity alpha beta gamma delta r
        rw [← v.1.2 r]
        apply congrArg Finset.card
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          exact (phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j).trans
            (congrArg pattern hj)
        · intro hj
          apply phi134_pattern_injective
          exact (phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j).symm.trans hj⟩
    invFun G := by
      let x : ProfileAddress N := fun l j ↦ pattern (G.1 j) l
      have hxSupport : CoordinatewiseSupported x := by
        intro j
        exact ⟨G.1 j, rfl⟩
      have hxMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ x l j = s)).card =
              marginalMultiplicity N alpha beta gamma delta l s := by
        intro l s
        change ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ pattern (G.1 j) l = s)).card = _
        rw [phi134_projectedFiberCard]
        calc
          (∑ r : {r : Fin 8 // pattern r l = s},
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r.1)).card) =
              ∑ r : {r : Fin 8 // pattern r l = s},
                multiplicity r.1 := by
                  apply Finset.sum_congr rfl
                  intro r _hr
                  rw [← Fintype.card_subtype]
                  exact G.2.2 r.1
          _ = marginalMultiplicity N alpha beta gamma delta l s :=
            hprofileSum l s
      let xm : MarginalAddress N alpha beta gamma delta :=
        ⟨x, hxSupport, hxMarginal⟩
      let xe : ExactProfileAddress N alpha beta gamma delta := ⟨xm, by
        intro r
        have hset :
            (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ addressType x j = pattern r) =
              (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change pattern (G.1 j) = pattern r ↔ G.1 j = r
          exact ⟨(fun h ↦ phi134_pattern_injective h), congrArg pattern⟩
        rw [hset, ← Fintype.card_subtype]
        exact G.2.2 r⟩
      refine ⟨xe, ?_⟩
      funext j
      exact G.2.1 j
    left_inv v := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      exact (congrFun
        (phi134_addressLabel_spec v.1.1.1 v.1.1.2.1 j) l).symm
    right_inv G := by
      apply Subtype.ext
      funext j
      apply phi134_pattern_injective
      simpa only using
        (phi134_addressLabel_spec
          (fun l j ↦ pattern (G.1 j) l) (fun j ↦ ⟨G.1 j, rfl⟩) j).symm
  }
  have hmarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w.1.1 l j = s)).card =
          marginalMultiplicity N alpha beta gamma delta l s :=
    w.1.2.2
  have hconstraint (s : Fin 5) :
      (∑ r : {r : Fin 8 // pattern r i = s}, multiplicity r.1) =
        Fintype.card {j : Fin (2 * N) // w.1.1 i j = s} := by
    rw [hprofileSum i s, Fintype.card_subtype, hmarginal i s]
  have hassignment :
      Nat.card Assignment =
        ∏ s : Fin 5,
          (Fintype.card {j : Fin (2 * N) // w.1.1 i j = s}).factorial /
            ∏ r : {r : Fin 8 // pattern r i = s},
              (multiplicity r.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := w.1.1 i) (q := fun r : Fin 8 ↦ pattern r i)
        multiplicity hconstraint)
  calc
    Nat.card
        {v : ExactProfileAddress N alpha beta gamma delta //
          v.1.1 i = w.1.1 i} = Nat.card Fiber := rfl
    _ = Nat.card Assignment := Nat.card_congr e
    _ = ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) // w.1.1 i j = s}).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (multiplicity r.1).factorial := hassignment
    _ = ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (multiplicity r.1).factorial := by
      apply Finset.prod_congr rfl
      intro s _hs
      rw [Fintype.card_subtype, hmarginal i s]
    _ = ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial := rfl
