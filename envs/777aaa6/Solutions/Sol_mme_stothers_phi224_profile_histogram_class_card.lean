-- Prove2me | solution 1 for mme_stothers_phi224_profile_histogram_class_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:24:23.674326+00:00
-- url     : https://prove2.me/submissions/fb4d6525-6fb9-4e1e-8212-6784869b6cd0

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

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

/-- A compatible fine histogram cuts out one multinomial stratum of the
full same-marginal phi_224 family. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (k : Fin 9 → ℕ)
    (hkTotal : (∑ r : Fin 9, k r) = 2 * N)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta //
          ∀ r : Fin 9,
            Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r} =
      (2 * N).factorial / ∏ r : Fin 9, (k r).factorial := by
  classical
  let Assignment :=
    {g : Fin (2 * N) → Fin 9 //
      ∀ r, Fintype.card {j // g j = r} = k r}
  let WordClass :=
    {b : MME.StothersFourth.Phi224.MarginalProfileWord
        N alpha beta gamma delta //
      ∀ r : Fin 9,
        Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r}
  let e : WordClass ≃ Assignment := {
    toFun b := ⟨b.1.1, b.2⟩
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
            exact G.2 r.1
          _ = MME.StothersFourth.Phi224.marginalMultiplicity
                alpha beta gamma delta l s := hkMarginal l s⟩
      exact ⟨b, G.2⟩
    left_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv G := by
      apply Subtype.ext
      rfl
  }
  have htotalCard :
      (∑ r : Fin 9, k r) = Fintype.card (Fin (2 * N)) := by
    simpa using hkTotal
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ ↦ Fintype.decidableForallFintype) Pi.instFintype
  have hcountGeneric : @Fintype.card Assignment ftGeneric =
      (2 * N).factorial / ∏ r : Fin 9, (k r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 9) k htotalCard)
  have hassignment : Nat.card Assignment =
      (2 * N).factorial / ∏ r : Fin 9, (k r).factorial := by
    calc
      Nat.card Assignment = @Fintype.card Assignment inferInstance :=
        Nat.card_eq_fintype_card
      _ = @Fintype.card Assignment ftGeneric :=
        @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
          (Equiv.refl Assignment)
      _ = _ := hcountGeneric
  calc
    Nat.card WordClass = Nat.card Assignment := Nat.card_congr e
    _ = (2 * N).factorial / ∏ r : Fin 9, (k r).factorial :=
      hassignment
