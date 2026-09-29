-- Prove2me | solution 1 for mme_stothers_general_mode_joint_table_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:25:59.767983+00:00
-- url     : https://prove2.me/submissions/241fb421-47f6-42be-8403-54fa0caf26f7

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace MME.StothersFourth

private theorem genHashExactFiber_card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (r : iota) :
    Fintype.card {x : alpha // q (g x) = r} =
      ∑ y : {y : beta // q y = r},
        Fintype.card {x : alpha // g x = y.1} := by
  classical
  let e : {x : alpha // q (g x) = r} ≃
      Sigma fun y : {y : beta // q y = r} ↦
        {x : alpha // g x = y.1} := {
    toFun x := ⟨⟨g x.1, x.2⟩, ⟨x.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by rw [x.2.2, x.1.2]⟩
    left_inv x := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
      cases hx
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem genHashExactFiber_prod_nat_div_eq_div_prod_of_dvd
    {iota : Type*} (s : Finset iota) (A B : iota → ℕ)
    (hdiv : ∀ i ∈ s, B i ∣ A i) :
    (∏ i ∈ s, A i / B i) =
      (∏ i ∈ s, A i) / ∏ i ∈ s, B i := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      have haDiv : B a ∣ A a := hdiv a (by simp)
      have hsDiv : ∀ i ∈ s, B i ∣ A i := by
        intro i hi
        exact hdiv i (by simp [hi])
      have hprodDiv : (∏ i ∈ s, B i) ∣ ∏ i ∈ s, A i :=
        Finset.prod_dvd_prod_of_dvd _ _ hsDiv
      simp only [Finset.prod_cons]
      rw [ih hsDiv, Nat.div_mul_div_comm haDiv hprodDiv]

private theorem genHashExactFiber_prod_over_coordinate
    (i : Fin 3) (f : GenHashSupportTriple → ℕ) :
    (∏ r : Fin 9,
      ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = r},
        f sigma.1) = ∏ sigma : GenHashSupportTriple, f sigma := by
  classical
  calc
    (∏ r : Fin 9,
        ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = r},
          f sigma.1) =
        ∏ x : Sigma fun r : Fin 9 ↦
          {sigma : GenHashSupportTriple // sigma.1 i = r},
          f x.2.1 := by
      exact (Fintype.prod_sigma
        (fun x : Sigma fun r : Fin 9 ↦
          {sigma : GenHashSupportTriple // sigma.1 i = r} ↦
            f x.2.1)).symm
    _ = ∏ sigma : GenHashSupportTriple, f sigma := by
      exact (Equiv.prod_comp
          (Equiv.sigmaFiberEquiv
            (fun sigma : GenHashSupportTriple ↦ sigma.1 i)) f)

end MME.StothersFourth

theorem solution
    (base : Fin 10 → ℕ) (m : ℕ)
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3)
    (k : MME.StothersFourth.GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.genMarginalCount base m j) :
    Nat.card
        {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
          b.1 i = a.1 i ∧
            MME.StothersFourth.genHashJointTable b = k} =
      (∏ j : Fin 9,
          (MME.StothersFourth.genMarginalCount base m j).factorial) /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
          (k sigma).factorial := by
  classical
  let Assignment :=
    {g : Fin (MME.StothersFourth.genOuterLength base m) →
        MME.StothersFourth.GenHashSupportTriple //
      (∀ j, (g j).1 i = a.1 i j) ∧
      ∀ sigma, Fintype.card {j // g j = sigma} = k sigma}
  let AddressClass :=
    {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
      b.1 i = a.1 i ∧
        MME.StothersFourth.genHashJointTable b = k}
  let e : AddressClass ≃ Assignment := {
    toFun b :=
      ⟨fun j ↦ MME.StothersFourth.genHashSupportedTypeAt b.1 j, by
        constructor
        · intro j
          change b.1.1 i j = a.1 i j
          exact congrFun b.2.1 j
        · intro sigma
          exact congrFun b.2.2 sigma⟩
    invFun G := by
      let raw : MME.StothersFourth.GenOuterAddress base m :=
        fun l j ↦ (G.1 j).1 l
      have hsupport : MME.StothersFourth.GenCoordinatewiseSupported raw := by
        intro j
        simpa only [raw] using (G.1 j).2
      have hmarginal : MME.StothersFourth.GenMarginallyRegular raw := by
        intro l r
        rw [← Fintype.card_subtype]
        change Fintype.card
          {j : Fin (MME.StothersFourth.genOuterLength base m) //
            (G.1 j).1 l = r} =
              MME.StothersFourth.genMarginalCount base m r
        rw [MME.StothersFourth.genHashExactFiber_card_composite_fiber G.1
          (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
            sigma.1 l) r]
        calc
          (∑ sigma :
              {sigma : MME.StothersFourth.GenHashSupportTriple //
                sigma.1 l = r},
              Fintype.card
                {j : Fin (MME.StothersFourth.genOuterLength base m) //
                  G.1 j = sigma.1}) =
              ∑ sigma :
                {sigma : MME.StothersFourth.GenHashSupportTriple //
                  sigma.1 l = r}, k sigma.1 := by
            apply Finset.sum_congr rfl
            intro sigma _
            exact G.2.2 sigma.1
          _ = MME.StothersFourth.genMarginalCount base m r :=
            hkMarginal l r
      let b : MME.StothersFourth.GenMarginalSupportedAddress base m :=
        ⟨raw, hsupport, hmarginal⟩
      refine ⟨b, ?_, ?_⟩
      · funext j
        exact G.2.1 j
      · funext sigma
        change Fintype.card
          {j : Fin (MME.StothersFourth.genOuterLength base m) //
            MME.StothersFourth.genHashSupportedTypeAt b j = sigma} =
              k sigma
        calc
          Fintype.card
              {j : Fin (MME.StothersFourth.genOuterLength base m) //
                MME.StothersFourth.genHashSupportedTypeAt b j = sigma} =
              Fintype.card
                {j : Fin (MME.StothersFourth.genOuterLength base m) //
                  G.1 j = sigma} := by
            apply Fintype.card_congr
            exact Equiv.subtypeEquiv (Equiv.refl _)
              (fun j ↦ by
                change
                  (⟨fun l ↦ (G.1 j).1 l, _⟩ :
                    MME.StothersFourth.GenHashSupportTriple) = sigma ↔
                      G.1 j = sigma
                constructor
                · intro h
                  exact Subtype.ext (congrArg Subtype.val h)
                · intro h
                  exact Subtype.ext (congrArg Subtype.val h))
          _ = k sigma := G.2.2 sigma
    left_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      rfl
    right_inv G := by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      rfl
  }
  have hsum (r : Fin 9) :
      (∑ sigma :
          {sigma : MME.StothersFourth.GenHashSupportTriple //
            sigma.1 i = r}, k sigma.1) =
        Fintype.card
          {j : Fin (MME.StothersFourth.genOuterLength base m) //
            a.1 i j = r} := by
    rw [Fintype.card_subtype]
    exact (hkMarginal i r).trans (a.2.2 i r).symm
  have hassignment : Nat.card Assignment =
      ∏ r : Fin 9,
        (Fintype.card
          {j : Fin (MME.StothersFourth.genOuterLength base m) //
            a.1 i j = r}).factorial /
          ∏ sigma :
            {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = r}, (k sigma.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := a.1 i)
        (q := fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
          sigma.1 i) k hsum)
  have hrowDiv (r : Fin 9) :
      (∏ sigma :
          {sigma : MME.StothersFourth.GenHashSupportTriple //
            sigma.1 i = r}, (k sigma.1).factorial) ∣
        (MME.StothersFourth.genMarginalCount base m r).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 i = r}) (fun sigma ↦ k sigma.1)
    simpa [hkMarginal i r] using h
  calc
    Nat.card AddressClass = Nat.card Assignment := Nat.card_congr e
    _ = ∏ r : Fin 9,
        (Fintype.card
          {j : Fin (MME.StothersFourth.genOuterLength base m) //
            a.1 i j = r}).factorial /
          ∏ sigma :
            {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = r}, (k sigma.1).factorial := hassignment
    _ = ∏ r : Fin 9,
        (MME.StothersFourth.genMarginalCount base m r).factorial /
          ∏ sigma :
            {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = r}, (k sigma.1).factorial := by
      apply Finset.prod_congr rfl
      intro r _
      rw [Fintype.card_subtype, a.2.2 i r]
    _ = (∏ r : Fin 9,
          (MME.StothersFourth.genMarginalCount base m r).factorial) /
        ∏ r : Fin 9,
          ∏ sigma :
            {sigma : MME.StothersFourth.GenHashSupportTriple //
              sigma.1 i = r}, (k sigma.1).factorial := by
      exact MME.StothersFourth.genHashExactFiber_prod_nat_div_eq_div_prod_of_dvd
        (Finset.univ : Finset (Fin 9))
        (fun r ↦ (MME.StothersFourth.genMarginalCount base m r).factorial)
        (fun r ↦ ∏ sigma :
          {sigma : MME.StothersFourth.GenHashSupportTriple //
            sigma.1 i = r}, (k sigma.1).factorial)
        (by
          intro r _
          exact hrowDiv r)
    _ = (∏ r : Fin 9,
          (MME.StothersFourth.genMarginalCount base m r).factorial) /
        ∏ sigma : MME.StothersFourth.GenHashSupportTriple,
          (k sigma).factorial := by
      exact congrArg
        (fun d : ℕ ↦
          (∏ r : Fin 9,
            (MME.StothersFourth.genMarginalCount base m r).factorial) / d)
        (MME.StothersFourth.genHashExactFiber_prod_over_coordinate i
          (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
            (k sigma).factorial))

