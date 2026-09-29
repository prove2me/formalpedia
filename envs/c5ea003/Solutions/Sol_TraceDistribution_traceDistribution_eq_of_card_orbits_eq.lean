-- Prove2me | solution 1 for TraceDistribution.traceDistribution_eq_of_card_orbits_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:36:02.243189+00:00
-- url     : https://prove2.me/submissions/f9721540-ed3d-4594-843b-9dc7ac385d1e

import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core

open MulAction Finset TraceDistribution Polynomial in
theorem solution {G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
    traceDistribution G X = traceDistribution G Y := by
  classical
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Y
  set K := max (Nat.card X) (Nat.card Y) with hK
  -- Burnside on tensor powers: power sums of fixed-point counts
  have hbX : ∀ k : ℕ, ∑ g : G, (fixedCard X g) ^ k = orbitCount G X k * Fintype.card G := by
    intro k
    have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin k → X)
    have e1 : ∀ g : G, Fintype.card (fixedBy (Fin k → X) g) = (fixedCard X g) ^ k := by
      intro g
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByPiEquiv X g k), Nat.card_fun,
        Nat.card_fin]
      rfl
    simp only [e1] at hb
    rw [hb, orbitCount, Nat.card_eq_fintype_card]
  have hbY : ∀ k : ℕ, ∑ g : G, (fixedCard Y g) ^ k = orbitCount G Y k * Fintype.card G := by
    intro k
    have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin k → Y)
    have e1 : ∀ g : G, Fintype.card (fixedBy (Fin k → Y) g) = (fixedCard Y g) ^ k := by
      intro g
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByPiEquiv Y g k), Nat.card_fun,
        Nat.card_fin]
      rfl
    simp only [e1] at hb
    rw [hb, orbitCount, Nat.card_eq_fintype_card]
  have hps : ∀ k ≤ K, ∑ g : G, ((fixedCard X g : ℕ) : ℚ) ^ k = ∑ g : G, ((fixedCard Y g : ℕ) : ℚ) ^ k := by
    intro k hk
    have := congrArg (fun m : ℕ => (m : ℚ)) ((hbX k).trans ((h k hk) ▸ (hbY k).symm))
    push_cast at this
    exact this
  have hleX : ∀ g : G, fixedCard X g ≤ K := fun g =>
    le_trans (Finite.card_subtype_le _) (le_max_left _ _)
  have hleY : ∀ g : G, fixedCard Y g ≤ K := fun g =>
    le_trans (Finite.card_subtype_le _) (le_max_right _ _)
  -- counts via Lagrange interpolation on the nodes `0, …, K`
  set s : Finset ℕ := range (K + 1) with hs
  have hinj : Set.InjOn (fun n : ℕ => (n : ℚ)) (s : Set ℕ) := fun a _ b _ hab =>
    Nat.cast_injective hab
  have hcount : ∀ (f : G → ℕ), (∀ g, f g ≤ K) → ∀ v, v ≤ K →
      (((univ.filter fun g => f g = v).card : ℕ) : ℚ)
        = ∑ i ∈ range (K + 1), (Lagrange.basis s (fun n : ℕ => (n : ℚ)) v).coeff i
            * ∑ g : G, ((f g : ℕ) : ℚ) ^ i := by
    intro f hf v hv
    have hvs : v ∈ s := Finset.mem_range.2 (by omega)
    have hdeg : (Lagrange.basis s (fun n : ℕ => (n : ℚ)) v).natDegree < K + 1 := by
      rw [Lagrange.natDegree_basis hinj hvs, hs, Finset.card_range]
      omega
    have heval : ∀ g : G, (Lagrange.basis s (fun n : ℕ => (n : ℚ)) v).eval ((f g : ℕ) : ℚ)
        = if f g = v then 1 else 0 := by
      intro g
      have hfg : f g ∈ s := Finset.mem_range.2 (by have := hf g; omega)
      split_ifs with hgv
      · rw [hgv]
        exact Lagrange.eval_basis_self hinj hvs
      · exact Lagrange.eval_basis_of_ne (Ne.symm hgv) hfg
    rw [Finset.card_filter, Nat.cast_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← eval_eq_sum_range' hdeg, heval]
    split_ifs <;> simp
  have hcnt : ∀ v, (univ.filter fun g : G => fixedCard X g = v).card
      = (univ.filter fun g : G => fixedCard Y g = v).card := by
    intro v
    by_cases hv : v ≤ K
    · have h1 := hcount (fun g : G => fixedCard X g) hleX v hv
      have h2 := hcount (fun g : G => fixedCard Y g) hleY v hv
      have h3 : (((univ.filter fun g : G => fixedCard X g = v).card : ℕ) : ℚ)
          = (((univ.filter fun g : G => fixedCard Y g = v).card : ℕ) : ℚ) := by
        rw [h1, h2]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hps i (by have := Finset.mem_range.1 hi; omega)]
      exact_mod_cast h3
    · rw [Finset.filter_false_of_mem (fun g _ => by have := hleX g; omega),
        Finset.filter_false_of_mem (fun g _ => by have := hleY g; omega)]
  unfold traceDistribution
  ext v
  rw [Multiset.count_map, Multiset.count_map]
  have eX : Multiset.card ((univ : Finset G).val.filter fun g => v = fixedCard X g)
      = (univ.filter fun g : G => fixedCard X g = v).card := by
    rw [Finset.filter_congr (fun g _ => (eq_comm : fixedCard X g = v ↔ v = fixedCard X g))]
    rfl
  have eY : Multiset.card ((univ : Finset G).val.filter fun g => v = fixedCard Y g)
      = (univ.filter fun g : G => fixedCard Y g = v).card := by
    rw [Finset.filter_congr (fun g _ => (eq_comm : fixedCard Y g = v ↔ v = fixedCard Y g))]
    rfl
  rw [eX, eY, hcnt v]
