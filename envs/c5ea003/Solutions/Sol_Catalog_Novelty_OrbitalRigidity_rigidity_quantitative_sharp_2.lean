-- Prove2me | solution 2 for Catalog.Novelty.OrbitalRigidity.rigidity_quantitative_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T09:11:36.03675+00:00
-- url     : https://prove2.me/submissions/39b8fcf8-1073-41af-be66-d05f28e70200

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
open Classical Catalog.Novelty.OrbitalRigidity MulAction Finset in
theorem solution {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Finite X] :
    (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ) * ((Nat.card X : ℚ) - (numOrbits G X : ℚ)) ^ 2
      ≤ ((Nat.card G : ℚ) - (Nat.card {g : G // ∀ x : X, g • x = x} : ℚ)) *
          ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2) := by
  haveI : Fintype X := Fintype.ofFinite X
  -- Burnside for `X` and for `X × X` (a pair is fixed iff both coordinates are)
  have hB1 : ∑ g : G, fixCount X g = numOrbits G X * Nat.card G := by
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  have hsq : ∀ g : G, fixCount (X × X) g = fixCount X g ^ 2 := by
    intro g
    unfold fixCount
    rw [sq, ← Nat.card_prod]
    refine Nat.card_congr ⟨fun p => ⟨⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩⟩, fun q => ⟨(q.1.1, q.2.1), ?_⟩,
      fun p => rfl, fun q => rfl⟩
    · have := p.2
      simp only [mem_fixedBy, Prod.smul_mk, Prod.ext_iff] at this
      exact this.1
    · have := p.2
      simp only [mem_fixedBy, Prod.smul_mk, Prod.ext_iff] at this
      exact this.2
    · simp only [mem_fixedBy, Prod.smul_mk, Prod.ext_iff]
      exact ⟨q.1.2, q.2.2⟩
  have hB2 : ∑ g : G, fixCount X g ^ 2 = numOrbits G (X × X) * Nat.card G := by
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G (X × X)
    rw [← sum_congr rfl (fun g _ => hsq g)]
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  -- expand the square and use both Burnside counts
  have q1 : ∑ g : G, (fixCount X g : ℚ) = (numOrbits G X : ℚ) * Nat.card G := by exact_mod_cast hB1
  have q2 : ∑ g : G, (fixCount X g : ℚ) ^ 2 = (numOrbits G (X × X) : ℚ) * Nat.card G := by
    exact_mod_cast hB2
  -- variance identity: `|G| (n₂ - n₁²) = Σ_g (fix g - n₁)²`
  have hvar : (Nat.card G : ℚ) * ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2)
      = ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2 := by
    have e : ∀ g : G, ((fixCount X g : ℚ) - numOrbits G X) ^ 2
        = (fixCount X g : ℚ) ^ 2 - 2 * (numOrbits G X : ℚ) * fixCount X g + (numOrbits G X : ℚ) ^ 2 :=
      fun g => by ring
    rw [sum_congr rfl (fun g _ => e g), sum_add_distrib, sum_sub_distrib, ← mul_sum, q1, q2,
      sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    ring
  -- trivial elements fix everything; the rest fix exactly `c` points
  set T := univ.filter (fun g : G => ∀ x : X, g • x = x) with hT
  have hfixT : ∀ g ∈ T, fixCount X g = Nat.card X := by
    intro g hg
    rw [mem_filter] at hg
    unfold fixCount
    have hu : fixedBy X g = Set.univ := Set.eq_univ_of_forall (fun x => hg.2 x)
    rw [hu, Nat.card_univ]
  have hcardN : (univ.filter (fun g : G => ¬ ∀ x : X, g • x = x)).card = Nat.card G - T.card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset G)) (fun g : G => ∀ x : X, g • x = x)
    rw [card_univ, ← Nat.card_eq_fintype_card] at this
    rw [hT]
    omega
  have hTcard : Nat.card {g : G // ∀ x : X, g • x = x} = T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hTle : T.card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact card_le_univ _
  set N := univ.filter (fun g : G => ¬ ∀ x : X, g • x = x) with hN
  set a : ℚ := (Nat.card X : ℚ) - (numOrbits G X : ℚ) with ha
  -- split both moments over trivial / non-trivial elements
  have hsq2 : ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2
      = (T.card : ℚ) * a ^ 2 + ∑ g ∈ N, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2 := by
    rw [← sum_filter_add_sum_filter_not univ (fun g : G => ∀ x : X, g • x = x)]
    congr 1
    rw [sum_congr rfl (fun g hg => by rw [hfixT g hg]), sum_const, nsmul_eq_mul]
  have hsq1 : ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ))
      = (T.card : ℚ) * a + ∑ g ∈ N, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) := by
    rw [← sum_filter_add_sum_filter_not univ (fun g : G => ∀ x : X, g • x = x)]
    congr 1
    rw [sum_congr rfl (fun g hg => by rw [hfixT g hg]), sum_const, nsmul_eq_mul]
  -- the centred first moment vanishes
  have hzero : ∑ g : G, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) = 0 := by
    rw [sum_sub_distrib, q1, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    ring
  -- Cauchy–Schwarz on the non-trivial elements
  have hcs := sq_sum_le_card_mul_sum_sq (s := N) (f := fun g => (fixCount X g : ℚ) - (numOrbits G X : ℚ))
  have hNcard : (N.card : ℚ) = (Nat.card G : ℚ) - T.card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset G)) (fun g : G => ∀ x : X, g • x = x)
    rw [card_univ, ← Nat.card_eq_fintype_card] at this
    rw [hN]
    have h' : ((univ.filter (fun g : G => ¬ ∀ x : X, g • x = x)).card : ℚ)
        = (Nat.card G : ℚ) - (T.card : ℚ) := by
      rw [hT]
      have := congrArg (fun n : ℕ => (n : ℚ)) this
      push_cast at this
      linarith
    exact h'
  have hGpos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos
  rw [hTcard]
  set S := ∑ g ∈ N, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) ^ 2 with hS
  set s1 := ∑ g ∈ N, ((fixCount X g : ℚ) - (numOrbits G X : ℚ)) with hs1
  have hs1v : s1 = -((T.card : ℚ) * a) := by linarith [hsq1, hzero]
  have hcs' : s1 ^ 2 ≤ ((Nat.card G : ℚ) - T.card) * S := by rw [← hNcard]; exact hcs
  have hvar' : (Nat.card G : ℚ) * ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2)
      = (T.card : ℚ) * a ^ 2 + S := by rw [hvar, hsq2]
  rw [hs1v] at hcs'
  have key : (Nat.card G : ℚ) * ((T.card : ℚ) * a ^ 2)
      ≤ (Nat.card G : ℚ) * (((Nat.card G : ℚ) - T.card) *
          ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2)) := by
    have hlhs : (Nat.card G : ℚ) * (((Nat.card G : ℚ) - T.card) *
        ((numOrbits G (X × X) : ℚ) - (numOrbits G X : ℚ) ^ 2))
        = ((Nat.card G : ℚ) - T.card) * ((T.card : ℚ) * a ^ 2 + S) := by
      rw [← hvar']
      ring
    rw [hlhs]
    nlinarith [hcs']
  exact le_of_mul_le_mul_left key hGpos
