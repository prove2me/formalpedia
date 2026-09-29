-- Prove2me | solution 1 for mme_stothers_fourth_table1_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T18:56:03.848059+00:00
-- url     : https://prove2.me/submissions/38f38026-e89d-4c94-aad6-5eec3b4ce113

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

namespace MME.StothersFourth


/-- The finite type of fourth-power grade triples whose entries sum to eight. -/
abbrev SupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

/-- A computational presentation of the six possible permutations of three
coordinates. -/
def sameOrbitExplicit (sigma rho : Fin 3 → Fin 9) : Prop :=
  (sigma 0 = rho 0 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 0 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 0) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 0)

instance instDecidableSameOrbitExplicit (sigma rho : Fin 3 → Fin 9) :
    Decidable (sameOrbitExplicit sigma rho) := by
  unfold sameOrbitExplicit
  infer_instance

private def perm012 : Equiv.Perm (Fin 3) :=
  Equiv.refl (Fin 3)

private def perm021 : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2

private def perm102 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

private def perm120 : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def perm201 : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 1)

private def perm210 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- On three coordinates, the abstract permutation-orbit relation is exactly
the explicit disjunction of its six possible coordinate arrangements. -/
theorem sameOrbit_iff_explicit (sigma rho : Fin 3 → Fin 9) :
    sameOrbit sigma rho ↔ sameOrbitExplicit sigma rho := by
  constructor
  · rintro ⟨e, he⟩
    have h01 : e 0 ≠ e 1 := by
      intro h
      have := e.injective h
      omega
    have h02 : e 0 ≠ e 2 := by
      intro h
      have := e.injective h
      omega
    have h12 : e 1 ≠ e 2 := by
      intro h
      have := e.injective h
      omega
    obtain ⟨e0, h0⟩ : ∃ e0 : Fin 3, e 0 = e0 := ⟨e 0, rfl⟩
    obtain ⟨e1, h1⟩ : ∃ e1 : Fin 3, e 1 = e1 := ⟨e 1, rfl⟩
    obtain ⟨e2, h2⟩ : ∃ e2 : Fin 3, e 2 = e2 := ⟨e 2, rfl⟩
    fin_cases e0 <;>
      fin_cases e1 <;>
      fin_cases e2 <;>
      simp_all [sameOrbitExplicit]
  · intro h
    rcases h with h | h | h | h | h | h
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm012, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm012]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm021, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm021, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm102, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm102, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm120, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm120, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm201, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm201, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm210, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm210, Equiv.swap_apply_def]

/-- There are exactly 45 ordered triples of grades in `{0, ..., 8}` whose
sum is eight. -/
theorem supportTriple_card : Fintype.card SupportTriple = 45 := by
  decide

/-- Every supported grade triple belongs to exactly one of the ten displayed
permutation classes. -/
theorem supportTriple_unique_class :
    ∀ sigma : SupportTriple,
      ∃! r : Fin 10, sameOrbit sigma.1 (classRep r) := by
  have hExists :
      ∀ sigma : SupportTriple,
        ∃ r : Fin 10, sameOrbitExplicit sigma.1 (classRep r) := by
    decide
  have hAtMostOne :
      ∀ (sigma : SupportTriple) (r₁ r₂ : Fin 10),
        sameOrbitExplicit sigma.1 (classRep r₁) →
          sameOrbitExplicit sigma.1 (classRep r₂) → r₁ = r₂ := by
    decide
  intro sigma
  rcases hExists sigma with ⟨r, hr⟩
  refine ⟨r, (sameOrbit_iff_explicit _ _).mpr hr, ?_⟩
  intro y hy
  exact hAtMostOne sigma y r ((sameOrbit_iff_explicit _ _).mp hy) hr

/-- The orbit of each displayed representative has the multiplicity recorded
in Table 1. -/
theorem supportTriple_orbit_card :
    ∀ r : Fin 10,
      Fintype.card
          {sigma : SupportTriple // sameOrbit sigma.1 (classRep r)} =
        3 * classMultiplicity r := by
  have hExplicit :
      ∀ r : Fin 10,
        Fintype.card
            {sigma : SupportTriple //
              sameOrbitExplicit sigma.1 (classRep r)} =
          3 * classMultiplicity r := by
    decide
  intro r
  rw [← hExplicit r]
  apply Fintype.card_congr
  exact
    { toFun := fun sigma ↦
        ⟨sigma.1, (sameOrbit_iff_explicit _ _).mp sigma.2⟩
      invFun := fun sigma ↦
        ⟨sigma.1, (sameOrbit_iff_explicit _ _).mpr sigma.2⟩
      left_inv := fun sigma ↦ Subtype.ext rfl
      right_inv := fun sigma ↦ Subtype.ext rfl }

end MME.StothersFourth

/-- Submission for the Table-1 enumeration child. -/
theorem solution :
    Fintype.card
        {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} = 45 ∧
    (∀ sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8},
      ∃! r : Fin 10,
        MME.StothersFourth.sameOrbit sigma.1
          (MME.StothersFourth.classRep r)) ∧
    (∀ r : Fin 10,
      Fintype.card
          {sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} //
            MME.StothersFourth.sameOrbit sigma.1
              (MME.StothersFourth.classRep r)} =
        3 * MME.StothersFourth.classMultiplicity r) := by
  exact ⟨
    MME.StothersFourth.supportTriple_card,
    MME.StothersFourth.supportTriple_unique_class,
    MME.StothersFourth.supportTriple_orbit_card⟩
