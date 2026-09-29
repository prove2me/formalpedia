-- Prove2me | solution 1 for mme_stothers_phi224_fixed_mode_histogram_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:24:23.573854+00:00
-- url     : https://prove2.me/submissions/c92eeb07-24ea-4ae4-b054-87f15751b152

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

private theorem card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (i : iota) :
    Fintype.card {a : alpha // q (g a) = i} =
      ∑ b : {b : beta // q b = i},
        Fintype.card {a : alpha // g a = b.1} := by
  classical
  let e : {a : alpha // q (g a) = i} ≃
      Sigma fun b : {b : beta // q b = i} ↦
        {a : alpha // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem prod_nat_div_eq_div_prod_of_dvd
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

/-- Once a mode word and a compatible fine histogram are fixed, the
phi_224 completion class is the product of five multinomial refinements. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi224.MarginalProfileWord
      N alpha beta gamma delta)
    (i : Fin 3) (k : Fin 9 → ℕ)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i ∧
            ∀ r : Fin 9,
              Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r} =
      (∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) /
        ∏ r : Fin 9, (k r).factorial := by
  classical
  let Assignment :=
    {g : Fin (2 * N) → Fin 9 //
      (∀ j,
        MME.StothersFourth.Phi224.pattern (g j) i =
          MME.StothersFourth.Phi224.modeWord a.1 i j) ∧
      ∀ r, Fintype.card {j // g j = r} = k r}
  let WordClass :=
    {b : MME.StothersFourth.Phi224.MarginalProfileWord
        N alpha beta gamma delta //
      MME.StothersFourth.Phi224.modeWord b.1 i =
          MME.StothersFourth.Phi224.modeWord a.1 i ∧
        ∀ r : Fin 9,
          Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r}
  let e : WordClass ≃ Assignment := {
    toFun b := ⟨b.1.1, by
      constructor
      · intro j
        exact congrFun b.2.1 j
      · exact b.2.2⟩
    invFun G := by
      let b : MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta := ⟨G.1, by
        intro l s
        rw [← Fintype.card_subtype]
        change Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.pattern (G.1 j) l = s} = _
        rw [card_composite_fiber G.1
          (fun r : Fin 9 ↦
            MME.StothersFourth.Phi224.pattern r l) s]
        calc
          (∑ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r l = s},
              Fintype.card {j : Fin (2 * N) // G.1 j = r.1}) =
              ∑ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r l = s},
                k r.1 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact G.2.2 r.1
          _ = MME.StothersFourth.Phi224.marginalMultiplicity
                alpha beta gamma delta l s := hkMarginal l s⟩
      refine ⟨b, ?_, G.2.2⟩
      funext j
      exact G.2.1 j
    left_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv G := by
      apply Subtype.ext
      rfl
  }
  have hsum (s : Fin 5) :
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s}, k r.1) =
        Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord a.1 i j = s} := by
    rw [Fintype.card_subtype]
    exact (hkMarginal i s).trans (a.2 i s).symm
  have hassignment : Nat.card Assignment =
      ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord a.1 i j = s}).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := MME.StothersFourth.Phi224.modeWord a.1 i)
        (q := fun r : Fin 9 ↦
          MME.StothersFourth.Phi224.pattern r i)
        k hsum)
  have hrowDiv (s : Fin 5) :
      (∏ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
          (k r.1).factorial) ∣
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s})
      (fun r ↦ k r.1)
    simpa [hkMarginal i s] using h
  calc
    Nat.card WordClass = Nat.card Assignment := Nat.card_congr e
    _ = ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord a.1 i j = s}).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial := hassignment
    _ = ∏ s : Fin 5,
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [Fintype.card_subtype, a.2 i s]
    _ = (∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) /
        ∏ s : Fin 5,
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial := by
      exact prod_nat_div_eq_div_prod_of_dvd
        (Finset.univ : Finset (Fin 5))
        (fun s ↦
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial)
        (fun s ↦ ∏ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
          (k r.1).factorial)
        (by
          intro s hs
          exact hrowDiv s)
    _ = (∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) /
        ∏ r : Fin 9, (k r).factorial := by
      congr 1
      calc
        (∏ s : Fin 5,
            ∏ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k r.1).factorial) =
            ∏ x : Sigma fun s : Fin 5 ↦
              {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k x.2.1).factorial := by
          exact (Fintype.prod_sigma
            (fun x : Sigma fun s : Fin 5 ↦
              {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s} ↦
              (k x.2.1).factorial)).symm
        _ = ∏ r : Fin 9, (k r).factorial := by
          simpa only using
            (Equiv.prod_comp
              (Equiv.sigmaFiberEquiv
                (fun r : Fin 9 ↦
                  MME.StothersFourth.Phi224.pattern r i))
              (fun r : Fin 9 ↦ (k r).factorial))
