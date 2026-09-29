-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.orbits_sq_eq_orbitals_card_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:16:37.386444+00:00
-- url     : https://prove2.me/submissions/f984db58-4489-4869-b90f-3cc7975bc110

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
open Classical Catalog.Novelty.OrbitalRigidity MulAction Finset in
theorem solution {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Finite X] :
    numOrbits G (X × X) = (numOrbits G X) ^ 2 ↔ ActsTrivially G X := by
  haveI : Fintype X := Fintype.ofFinite X
  -- a pair is fixed iff both coordinates are: `fix_{X×X}(g) = fix(g)²`
  have hfix2 : ∀ g : G, fixCount (X × X) g = fixCount X g ^ 2 := by
    intro g
    unfold fixCount
    rw [sq, ← Nat.card_prod]
    refine Nat.card_congr ⟨fun p => (⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩),
      fun q => ⟨(q.1.1, q.2.1), ?_⟩, fun p => rfl, fun q => rfl⟩
    · have := p.2
      rw [mem_fixedBy] at this ⊢
      exact congrArg Prod.fst this
    · have := p.2
      rw [mem_fixedBy] at this ⊢
      exact congrArg Prod.snd this
    · rw [mem_fixedBy]
      have h1 := q.1.2
      have h2 := q.2.2
      rw [mem_fixedBy] at h1 h2
      exact Prod.ext h1 h2
  -- Burnside for `X` and for `X × X`
  have hB1 : ∑ g : G, fixCount X g = numOrbits G X * Nat.card G := by
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  have hB2 : ∑ g : G, fixCount X g ^ 2 = numOrbits G (X × X) * Nat.card G := by
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G (X × X)
    rw [← sum_congr rfl (fun g _ => hfix2 g)]
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  have hGpos : 0 < Nat.card G := Nat.card_pos
  constructor
  · -- a non-trivial action has `n₂ > n₁²`: `(Σ fix)² < |G| Σ fix²` for non-constant `fix`
    intro heq
    by_contra h
    obtain ⟨g₀, x₀, hx₀⟩ : ∃ g₀ : G, ∃ x₀ : X, g₀ • x₀ ≠ x₀ := by
      by_contra hne
      push_neg at hne
      exact h hne
    have hfix1 : fixCount X (1 : G) = Nat.card X := by
      unfold fixCount
      have hu : fixedBy X (1 : G) = Set.univ := Set.eq_univ_of_forall (fun x => one_smul G x)
      rw [hu, Nat.card_univ]
    have hfixlt : fixCount X g₀ < Nat.card X := by
      unfold fixCount
      exact Finite.card_subtype_lt (p := fun x => x ∈ fixedBy X g₀) (x := x₀)
        (by show ¬ (x₀ ∈ fixedBy X g₀); rw [mem_fixedBy]; exact hx₀)
    have hpair : 0 < ∑ g : G, ∑ g' : G, ((fixCount X g : ℤ) - fixCount X g') ^ 2 := by
      refine sum_pos' (fun g _ => sum_nonneg fun g' _ => sq_nonneg _) ⟨1, mem_univ _, ?_⟩
      refine sum_pos' (fun g' _ => sq_nonneg _) ⟨g₀, mem_univ _, ?_⟩
      rw [hfix1]
      have : (fixCount X g₀ : ℤ) < Nat.card X := by exact_mod_cast hfixlt
      nlinarith
    have hexp : ∑ g : G, ∑ g' : G, ((fixCount X g : ℤ) - fixCount X g') ^ 2
        = 2 * (Nat.card G : ℤ) * ∑ g : G, (fixCount X g : ℤ) ^ 2
          - 2 * (∑ g : G, (fixCount X g : ℤ)) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← mul_sum, ← sum_mul, Nat.card_eq_fintype_card]
      ring
    have q1 : ∑ g : G, (fixCount X g : ℤ) = (numOrbits G X : ℤ) * Nat.card G := by
      exact_mod_cast hB1
    have q2 : ∑ g : G, (fixCount X g : ℤ) ^ 2 = (numOrbits G (X × X) : ℤ) * Nat.card G := by
      exact_mod_cast hB2
    rw [hexp, q1, q2] at hpair
    have hGz : (0 : ℤ) < Nat.card G := by exact_mod_cast hGpos
    have heqz : (numOrbits G (X × X) : ℤ) = (numOrbits G X : ℤ) ^ 2 := by exact_mod_cast heq
    rw [heqz] at hpair
    nlinarith
  · -- a trivial action fixes everything: `n₁ = |X|`, `n₂ = |X|²`
    intro htriv
    have hall : ∀ g : G, fixCount X g = Nat.card X := by
      intro g
      unfold fixCount
      have hu : fixedBy X g = Set.univ := Set.eq_univ_of_forall (fun x => htriv g x)
      rw [hu, Nat.card_univ]
    simp only [hall, sum_const, card_univ, smul_eq_mul] at hB1 hB2
    rw [← Nat.card_eq_fintype_card] at hB1 hB2
    have h1 : numOrbits G X = Nat.card X := by
      apply Nat.eq_of_mul_eq_mul_right hGpos
      rw [← hB1, mul_comm]
    have h2 : numOrbits G (X × X) = Nat.card X ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hGpos
      rw [← hB2, mul_comm]
    rw [h1, h2]
