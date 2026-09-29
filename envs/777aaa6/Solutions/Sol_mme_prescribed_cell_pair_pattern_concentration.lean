-- Prove2me | solution 1 for mme_prescribed_cell_pair_pattern_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:10:59.726631+00:00
-- url     : https://prove2.me/submissions/f73af01d-3f83-459c-a421-61232a5fd074

import Theorems.Thm_mme_prescribed_cell_sampling_pattern_approximation
import Theorems.Thm_mme_finite_pair_moment_concentration

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem solution {P C W T : Type*} [Fintype P] [Fintype W] [Fintype T]
    (cell : P → C) (mu : C → W → ℕ) (q : T × Fin 2 → P) (hq : Function.Injective q)
    (w : Fin 2 → W) (hU : Nonempty {f : P → W // Useful cell mu f})
    (m : ℕ) (hm : 0 < m) (hmn : m ≤ Fintype.card T)
    (hsize : ∀ t h, m ≤ Fintype.card {p : P // cell p = cell (q (t,h))})
    (eps : ℝ) (heps : 0 < eps) :
    (𝔼 f : {f : P → W // Useful cell mu f},
      if eps ≤ |((∑ t : T, if (∀ h : Fin 2, f.val (q (t,h)) = w h) then (1 : ℝ) else 0) -
        ∑ t : T, ∏ h : Fin 2, ((mu (cell (q (t,h))) (w h) : ℝ) /
          Fintype.card {p : P // cell p = cell (q (t,h))})) / Fintype.card T|
      then (1 : ℝ) else 0) ≤ 25 / ((m : ℝ) * eps ^ 2) := by
  classical
  let U := {f : P → W // Useful cell mu f}
  letI : Nonempty U := hU
  let Z (t : T) (f : U) : ℝ := if ∀ h : Fin 2, f.val (q (t,h)) = w h then 1 else 0
  let a (t : T) : ℝ := ∏ h : Fin 2, ((mu (cell (q (t,h))) (w h) : ℝ) /
      Fintype.card {p : P // cell p = cell (q (t,h))})
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ Fintype.card T := by exact_mod_cast hmn
  have hZ (t : T) (f : U) : 0 ≤ Z t f ∧ Z t f ≤ 1 := by dsimp [Z]; split_ifs <;> norm_num
  let f0 := Classical.choice hU
  have hmu (c : C) (v : W) : mu c v ≤ Fintype.card {p : P // cell p = c} := by
    rw [← f0.property c v, Fintype.card_subtype]
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
  have ha (t : T) : 0 ≤ a t ∧ a t ≤ 1 := by
    have hv (h : Fin 2) : 0 ≤ ((mu (cell (q (t,h))) (w h) : ℝ) /
        Fintype.card {p : P // cell p = cell (q (t,h))}) ∧
        ((mu (cell (q (t,h))) (w h) : ℝ) /
        Fintype.card {p : P // cell p = cell (q (t,h))}) ≤ 1 := by
      have hp : (0 : ℝ) < Fintype.card {p : P // cell p = cell (q (t,h))} := by
        exact_mod_cast (hm.trans_le (hsize t h))
      constructor
      · positivity
      · apply (div_le_one hp).mpr
        exact_mod_cast hmu (cell (q (t,h))) (w h)
    exact ⟨Finset.prod_nonneg (fun h _ ↦ (hv h).1), Finset.prod_le_one (fun h _ ↦ (hv h).1) (fun h _ ↦ (hv h).2)⟩
  have hfirst (t : T) : |(𝔼 f, Z t f) - a t| ≤ 4 / (m : ℝ) := by
    have ht : Function.Injective (fun h : Fin 2 ↦ q (t,h)) := by
      intro x y h; exact congrArg Prod.snd (hq h)
    simpa only [Z, a, Fin.forall_fin_two, Fintype.card_fin, Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      mme_prescribed_cell_sampling_pattern_approximation cell mu (fun h ↦ q (t,h)) ht w
        hU m hm (hsize t)
  have hsecond (t s : T) (hts : t ≠ s) :
      |(𝔼 f, Z t f * Z s f) - a t * a s| ≤ 16 / (m : ℝ) := by
    let quad (j : Fin 2 × Fin 2) := q (if j.1 = 0 then t else s, j.2)
    have hquad : Function.Injective quad := by
      rintro ⟨i,k⟩ ⟨j,l⟩ he
      fin_cases i <;> fin_cases j
      · change q (t,k) = q (t,l) at he
        exact Prod.ext rfl (congrArg (fun z : T × Fin 2 ↦ z.2) (hq he))
      · change q (t,k) = q (s,l) at he
        exact (hts (congrArg Prod.fst (hq he))).elim
      · change q (s,k) = q (t,l) at he
        exact (hts (congrArg Prod.fst (hq he)).symm).elim
      · change q (s,k) = q (s,l) at he
        exact Prod.ext rfl (congrArg (fun z : T × Fin 2 ↦ z.2) (hq he))
    have hsq (j : Fin 2 × Fin 2) : m ≤ Fintype.card {p : P // cell p = cell (quad j)} :=
      hsize _ _
    have hp := mme_prescribed_cell_sampling_pattern_approximation cell mu quad hquad
      (fun j ↦ w j.2) hU m hm hsq
    have hpat (f : U) : (if (∀ j : Fin 2 × Fin 2, f.val (quad j) = w j.2) then (1 : ℝ) else 0) =
        Z t f * Z s f := by
      simp only [Prod.forall, Fin.forall_fin_two, quad, Z, Fin.isValue, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide]
      split_ifs <;> simp_all
    have hprod : (∏ j : Fin 2 × Fin 2, ((mu (cell (quad j)) (w j.2) : ℝ) /
        Fintype.card {p : P // cell p = cell (quad j)})) = a t * a s := by
      simp only [Fintype.prod_prod_type, Fin.prod_univ_two, quad, a, Fin.isValue, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide]
    simp only [hpat, hprod, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, show ((2 : ℝ) * 2) ^ 2 = 16 by norm_num] at hp
    exact hp
  exact mme_finite_pair_moment_concentration Z a m eps hm' hmn' heps hZ ha hfirst hsecond
