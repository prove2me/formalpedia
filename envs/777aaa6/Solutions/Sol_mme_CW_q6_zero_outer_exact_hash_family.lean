-- Prove2me | solution 1 for mme_CW_q6_zero_outer_exact_hash_family
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:05:36.667127+00:00
-- url     : https://prove2.me/submissions/caba82c0-f8c0-4c06-9426-39a2964fe45c

import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
import Mathlib.Tactic.FinCases

open MME

private theorem zero_outer_z {N : ℕ} (a : CWQ6ExactCoupledAddress N 0 N)
    (j : Fin (2 * N)) : a.val 2 j = 2 := by
  have h0 : ∀ j, a.val 2 j ≠ 0 := by
    simpa [cwQ6CoupledMarginalMultiplicity, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff] using a.property.2 2 0
  have h1 : ∀ j, a.val 2 j ≠ 1 := by
    simpa [cwQ6CoupledMarginalMultiplicity, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff] using a.property.2 2 1
  have hlt := (a.val 2 j).isLt
  apply Fin.ext
  have := h0 j
  have := h1 j
  simp only [ne_eq, Fin.ext_iff] at *
  omega

private theorem zero_outer_x_injective {N : ℕ} :
    Function.Injective (fun a : CWQ6ExactCoupledAddress N 0 N => a.val 0) := by
  intro a b hab
  apply Subtype.ext
  funext i j
  have ha := a.property.1 j
  have hb := b.property.1 j
  have hx := congrFun hab j
  have hza := zero_outer_z a j
  have hzb := zero_outer_z b j
  fin_cases i
  · exact hx
  · rcases ha with ha | ha | ha | ha <;>
      rcases hb with hb | hb | hb | hb <;> simp_all
  · exact hza.trans hzb.symm

private theorem zero_outer_y_injective {N : ℕ} :
    Function.Injective (fun a : CWQ6ExactCoupledAddress N 0 N => a.val 1) := by
  intro a b hab
  apply Subtype.ext
  funext i j
  have ha := a.property.1 j
  have hb := b.property.1 j
  have hy := congrFun hab j
  have hza := zero_outer_z a j
  have hzb := zero_outer_z b j
  fin_cases i
  · rcases ha with ha | ha | ha | ha <;>
      rcases hb with hb | hb | hb | hb <;> simp_all
  · exact hy
  · exact hza.trans hzb.symm

/-- At zero outer mass all exact addresses form one induced star, with
one middle entry for each balanced binary word. No pruning is needed. -/
theorem solution (N : ℕ) :
    Nonempty (CWQ6PrimaryHashFamily N 0 N 1 (Nat.choose (2 * N) N)) := by
  classical
  let E := cwQ6ExactAddresses N 0 N
  have hcard : E.card = Nat.choose (2 * N) N := by
    simpa [E] using (mme_CW_q6_exact_coupled_address_regularity N 0 N (by omega)).total_card
  let index : Fin (Nat.choose (2 * N) N) ≃ E := (E.equivFinOfCardEq hcard).symm
  let entry (p : Fin 1 × Fin (Nat.choose (2 * N) N)) : CWQ6ExactCoupledAddress N 0 N :=
    ⟨(index p.2).val, (Finset.mem_filter.mp (index p.2).property).2⟩
  have hinj : Function.Injective entry := by
    intro p q h
    apply Prod.ext (Subsingleton.elim _ _)
    apply index.injective
    apply Subtype.ext
    exact congrArg (fun a : CWQ6ExactCoupledAddress N 0 N => a.val) h
  refine ⟨{ hHpos := Nat.choose_pos (by omega)
            entry := entry
            xInjective := zero_outer_x_injective.comp hinj
            yInjective := zero_outer_y_injective.comp hinj
            zSameFiber := ?_
            zSeparatesFibers := ?_
            induced := ?_ }⟩
  · intro a h k
    funext j
    exact (zero_outer_z (entry (a, h)) j).trans (zero_outer_z (entry (a, k)) j).symm
  · intro a b h k _
    exact Subsingleton.elim _ _
  · intro p q r h
    have hpq : (entry p).val 0 = (entry q).val 0 := by
      funext j
      have hm := h j
      have hq := (entry q).property.1 j
      have hzr := zero_outer_z (entry r) j
      have hzq := zero_outer_z (entry q) j
      simp only [cwQ6CoupledMixedAddress] at hm
      rcases hm with hm | hm | hm | hm <;>
        rcases hq with hq | hq | hq | hq <;> simp_all
    exact ⟨hinj (zero_outer_x_injective hpq), Subsingleton.elim _ _⟩


#print axioms solution
