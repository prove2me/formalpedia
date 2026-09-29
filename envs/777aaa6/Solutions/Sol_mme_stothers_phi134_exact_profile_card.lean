-- Prove2me | solution 1 for mme_stothers_phi134_exact_profile_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:15:49.273124+00:00
-- url     : https://prove2.me/submissions/1086765f-2f65-4a4a-bec7-eb9d8209149d

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace MME.StothersFourth.Phi134ExactCard

private theorem pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def addressLabel
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem addressLabel_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (addressLabel x hx j) :=
  Classical.choose_spec (hx j)

private theorem projectedFiberCard
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

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

private theorem profile_sum
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (l : Fin 3) (s : Fin 5) :
    (∑ r : {r : Fin 8 // pattern r l = s},
        profileMultiplicity alpha beta gamma delta r.1) =
      marginalMultiplicity N alpha beta gamma delta l s := by
  rw [← sum_ite_eq_sum_subtype
    (fun r : Fin 8 ↦ pattern r l) s
      (profileMultiplicity alpha beta gamma delta)]
  fin_cases l <;> fin_cases s <;>
    simp [pattern, profileMultiplicity, marginalMultiplicity,
      MME.cwSquareBlockType, Fin.sum_univ_succ] <;> omega

end MME.StothersFourth.Phi134ExactCard

/-- Development form of the exact symmetric eight-pattern cardinality. -/
theorem mme_stothers_phi134_exact_profile_card_local
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    Nat.card
        (ExactProfileAddress N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := by
  classical
  let multiplicity : Fin 8 → ℕ :=
    profileMultiplicity alpha beta gamma delta
  have htotal : (∑ r : Fin 8, multiplicity r) = 2 * N := by
    simp [multiplicity, profileMultiplicity, Fin.sum_univ_succ]
    omega
  have htotalCard :
      (∑ r : Fin 8, multiplicity r) = Fintype.card (Fin (2 * N)) := by
    simpa using htotal
  let Assignment :=
    {g : Fin (2 * N) → Fin 8 //
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ => Fintype.decidableForallFintype) Pi.instFintype
  have hgeneric :
      @Fintype.card Assignment ftGeneric =
        (2 * N).factorial / ∏ r : Fin 8, (multiplicity r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 8) multiplicity htotalCard)
  let e : ExactProfileAddress N alpha beta gamma delta ≃ Assignment := {
    toFun w := ⟨fun j ↦
      MME.StothersFourth.Phi134ExactCard.addressLabel
        w.1.1 w.1.2.1 j, by
      intro r
      rw [Fintype.card_subtype]
      change _ = profileMultiplicity alpha beta gamma delta r
      rw [← w.2 r]
      apply congrArg Finset.card
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        exact (MME.StothersFourth.Phi134ExactCard.addressLabel_spec
          w.1.1 w.1.2.1 j).trans (congrArg pattern hj)
      · intro hj
        apply MME.StothersFourth.Phi134ExactCard.pattern_injective
        exact (MME.StothersFourth.Phi134ExactCard.addressLabel_spec
          w.1.1 w.1.2.1 j).symm.trans hj⟩
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
        rw [MME.StothersFourth.Phi134ExactCard.projectedFiberCard]
        calc
          (∑ r : {r : Fin 8 // pattern r l = s},
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r.1)).card) =
              ∑ r : {r : Fin 8 // pattern r l = s},
                multiplicity r.1 := by
                  apply Finset.sum_congr rfl
                  intro r _hr
                  rw [← Fintype.card_subtype]
                  exact G.2 r.1
          _ = marginalMultiplicity N alpha beta gamma delta l s :=
            MME.StothersFourth.Phi134ExactCard.profile_sum
              N alpha beta gamma delta hsum l s
      let xm : MarginalAddress N alpha beta gamma delta :=
        ⟨x, hxSupport, hxMarginal⟩
      exact ⟨xm, by
        intro r
        have hset :
            (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ addressType x j = pattern r) =
              (Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change pattern (G.1 j) = pattern r ↔ G.1 j = r
          exact ⟨
            fun h ↦ MME.StothersFourth.Phi134ExactCard.pattern_injective h,
            congrArg pattern⟩
        rw [hset, ← Fintype.card_subtype]
        exact G.2 r⟩
    left_inv w := by
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      exact (congrFun
        (MME.StothersFourth.Phi134ExactCard.addressLabel_spec
          w.1.1 w.1.2.1 j) l).symm
    right_inv G := by
      apply Subtype.ext
      funext j
      apply MME.StothersFourth.Phi134ExactCard.pattern_injective
      simpa only using
        (MME.StothersFourth.Phi134ExactCard.addressLabel_spec
          (fun l j ↦ pattern (G.1 j) l)
          (fun j ↦ ⟨G.1 j, rfl⟩) j).symm
  }
  calc
    Nat.card (ExactProfileAddress N alpha beta gamma delta) =
        Nat.card Assignment := Nat.card_congr e
    _ = @Fintype.card Assignment inferInstance := Nat.card_eq_fintype_card
    _ = @Fintype.card Assignment ftGeneric :=
      @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
        (Equiv.refl Assignment)
    _ = (2 * N).factorial /
        ∏ r : Fin 8, (multiplicity r).factorial := hgeneric
    _ = (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := rfl

/-- The number of exact symmetric eight-pattern Phi134 profile addresses. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    Nat.card
        (ExactProfileAddress N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 8,
          (profileMultiplicity alpha beta gamma delta r).factorial := by
  exact mme_stothers_phi134_exact_profile_card_local
    N alpha beta gamma delta hsum
