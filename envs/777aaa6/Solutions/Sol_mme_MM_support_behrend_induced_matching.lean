-- Prove2me | solution 1 for mme_MM_support_behrend_induced_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:23:50.59494+00:00
-- url     : https://prove2.me/submissions/f31668c1-8434-431c-b97e-e3db4160663d

import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision

open Real

set_option maxHeartbeats 1600000

private theorem mme_MM_behrend_rate_bound_large
    (H : ℕ) (hH : 4 ≤ H) :
    let M := H / 4
    let R := H - 2 * M
    ((H : ℝ) ^ 2) *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
      (R : ℝ) * (M : ℝ) *
        Real.exp (-4 * Real.sqrt (Real.log M)) := by
  dsimp only
  let M := H / 4
  let r := H % 4
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.div_pos hH (by omega)
  have hrlt : r < 4 := by
    exact Nat.mod_lt H (by omega)
  have hdecomp : r + 4 * M = H := by
    simpa [M, r] using Nat.mod_add_div H 4
  have htwiceM : 2 * M ≤ H := by omega
  have hR : H - 2 * M = 2 * M + r := by omega
  have hcoeffNat : H ^ 2 ≤ 10 * ((H - 2 * M) * M) := by
    rw [hR]
    nlinarith
  have hcoeff : (H : ℝ) ^ 2 ≤
      10 * (((H - 2 * M : ℕ) : ℝ) * (M : ℝ)) := by
    exact_mod_cast hcoeffNat
  have hMle : (M : ℝ) ≤ (((H + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show M ≤ H + 1 by omega)
  have hlogMono : Real.log (M : ℝ) ≤
      Real.log (((H + 1 : ℕ) : ℝ)) := by
    exact Real.log_le_log (by exact_mod_cast hMpos) hMle
  have hsqrtMono : Real.sqrt (Real.log (M : ℝ)) ≤
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) := by
    exact Real.sqrt_le_sqrt hlogMono
  have hlogOne : (1 : ℝ) ≤
      Real.log (((H + 1 : ℕ) : ℝ)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact (le_of_lt Real.exp_one_lt_three).trans (by
      exact_mod_cast (show 3 ≤ H + 1 by omega))
  have hsqrtOne : (1 : ℝ) ≤
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlogOne
  have hexp :
      10 * Real.exp
          (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        Real.exp (-4 * Real.sqrt (Real.log (M : ℝ))) := by
    calc
      10 * Real.exp
            (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
          ≤ 97 * Real.exp
            (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
              gcongr
              norm_num
      _ ≤ Real.exp 96 * Real.exp
            (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
              gcongr
              convert Real.add_one_le_exp (96 : ℝ) using 1 <;> norm_num
      _ = Real.exp
            (96 - 100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
              rw [← Real.exp_add]
              congr 1
              ring
      _ ≤ Real.exp (-4 * Real.sqrt (Real.log (M : ℝ))) := by
              apply Real.exp_le_exp.mpr
              nlinarith
  calc
    ((H : ℝ) ^ 2) *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
        ≤ (10 * (((H - 2 * M : ℕ) : ℝ) * (M : ℝ))) *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
            gcongr
    _ = (((H - 2 * M : ℕ) : ℝ) * (M : ℝ)) *
          (10 * Real.exp
            (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) := by ring
    _ ≤ (((H - 2 * M : ℕ) : ℝ) * (M : ℝ)) *
          Real.exp (-4 * Real.sqrt (Real.log (M : ℝ))) := by
            gcongr
    _ = ((H - 2 * (H / 4) : ℕ) : ℝ) * ((H / 4 : ℕ) : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log (H / 4 : ℕ))) := by
            rfl

private theorem mme_MM_behrend_rate_bound_small
    (H : ℕ) (hHpos : 0 < H) (hHsmall : H < 4) :
    ((H : ℝ) ^ 2) *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
      1 := by
  by_cases hHone : H = 1
  · subst H
    norm_num only [Nat.cast_ofNat, one_pow, one_mul]
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [Real.sqrt_nonneg (Real.log (2 : ℝ))])
  · have hHtwo : 2 ≤ H := by omega
    have hcoeff : (H : ℝ) ^ 2 ≤ 9 := by
      rcases (show H = 2 ∨ H = 3 by omega) with rfl | rfl <;> norm_num
    have hlogOne : (1 : ℝ) ≤
        Real.log (((H + 1 : ℕ) : ℝ)) := by
      apply (Real.le_log_iff_exp_le (by positivity)).2
      exact (le_of_lt Real.exp_one_lt_three).trans (by
        exact_mod_cast (show 3 ≤ H + 1 by omega))
    have hsqrtOne : (1 : ℝ) ≤
        Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hlogOne
    have hexp : Real.exp
        (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (1 : ℝ) / 101 := by
      have h101 : (101 : ℝ) ≤ Real.exp 100 := by
        convert Real.add_one_le_exp (100 : ℝ) using 1 <;> norm_num
      have hpos : 0 < Real.exp (100 : ℝ) := Real.exp_pos 100
      have hinv : Real.exp (-100) ≤ (1 : ℝ) / 101 := by
        rw [Real.exp_neg]
        simpa [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 101) h101
      exact (Real.exp_le_exp.mpr (by nlinarith)).trans hinv
    calc
      ((H : ℝ) ^ 2) *
            Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
          ≤ 9 * ((1 : ℝ) / 101) := by gcongr
      _ ≤ 1 := by norm_num

theorem solution
    (H : ℕ) (hH : 0 < H) :
    ∃ E : Finset (Fin H × Fin H × Fin H),
      Function.Injective
        (fun e : E => (e.1.1, e.1.2.1)) ∧
      Function.Injective
        (fun e : E => (e.1.2.1, e.1.2.2)) ∧
      Function.Injective
        (fun e : E => (e.1.2.2, e.1.1)) ∧
      (∀ x y z : E,
        x.1.2.1 = y.1.2.1 →
        y.1.2.2 = z.1.2.2 →
        z.1.1 = x.1.1 →
        x = y ∧ y = z) ∧
      ((H : ℝ) ^ 2) *
          Real.exp (-100 *
            Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) ≤
        (E.card : ℝ) := by
  classical
  by_cases hlarge : 4 ≤ H
  · let M : ℕ := H / 4
    let R : ℕ := H - 2 * M
    have hMpos : 0 < M := by
      dsimp only [M]
      omega
    have hfourM : 4 * M ≤ H := by
      dsimp only [M]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self H 4
    have htwoM : 2 * M ≤ H := by omega
    obtain ⟨S, hSrange, hSfree, hScard⟩ :=
      mme_behrend_explicit_threeAP_free M
    let P : Finset (ℕ × ℕ) := (Finset.range R).product S
    have hp_bounds (p : P) :
        p.1.1 < R ∧ p.1.2 < M := by
      have hp := Finset.mem_product.mp p.2
      exact ⟨Finset.mem_range.mp hp.1,
        Finset.mem_range.mp (hSrange hp.2)⟩
    have hx0 (p : P) : p.1.1 < H := by
      have hp := hp_bounds p
      dsimp only [R] at hp
      omega
    have hx1 (p : P) : p.1.1 + p.1.2 < H := by
      have hp := hp_bounds p
      dsimp only [R] at hp
      omega
    have hx2 (p : P) : p.1.1 + 2 * p.1.2 < H := by
      have hp := hp_bounds p
      dsimp only [R] at hp
      omega
    let phi : P → Fin H × Fin H × Fin H := fun p =>
      (⟨p.1.1, hx0 p⟩,
        ⟨p.1.1 + p.1.2, hx1 p⟩,
        ⟨p.1.1 + 2 * p.1.2, hx2 p⟩)
    let E : Finset (Fin H × Fin H × Fin H) := P.attach.image phi
    have hphi_injective : Function.Injective phi := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun t => (t.1 : ℕ)) hpq
      · have hfirst := congrArg (fun t => (t.1 : ℕ)) hpq
        have hsecond := congrArg (fun t => (t.2.1 : ℕ)) hpq
        dsimp only [phi] at hfirst hsecond
        omega
    have hcardE : E.card = R * S.card := by
      dsimp only [E]
      rw [Finset.card_image_of_injective _ hphi_injective,
        Finset.card_attach]
      simp [P]
    refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      obtain ⟨pa, hpaP, hpa⟩ := Finset.mem_image.mp a.2
      obtain ⟨pb, hpbP, hpb⟩ := Finset.mem_image.mp b.2
      dsimp only at hab
      rw [← hpa, ← hpb] at hab
      have hfirst := congrArg (fun t => (t.1 : ℕ)) hab
      have hsecond := congrArg (fun t => (t.2 : ℕ)) hab
      dsimp only [phi] at hfirst hsecond
      have hpval : pa.1 = pb.1 := by
        apply Prod.ext <;> omega
      have hp : pa = pb := Subtype.ext hpval
      apply Subtype.ext
      rw [← hpa, ← hpb, hp]
    · intro a b hab
      obtain ⟨pa, hpaP, hpa⟩ := Finset.mem_image.mp a.2
      obtain ⟨pb, hpbP, hpb⟩ := Finset.mem_image.mp b.2
      dsimp only at hab
      rw [← hpa, ← hpb] at hab
      have hsecond := congrArg (fun t => (t.1 : ℕ)) hab
      have hthird := congrArg (fun t => (t.2 : ℕ)) hab
      dsimp only [phi] at hsecond hthird
      have hpval : pa.1 = pb.1 := by
        apply Prod.ext <;> omega
      have hp : pa = pb := Subtype.ext hpval
      apply Subtype.ext
      rw [← hpa, ← hpb, hp]
    · intro a b hab
      obtain ⟨pa, hpaP, hpa⟩ := Finset.mem_image.mp a.2
      obtain ⟨pb, hpbP, hpb⟩ := Finset.mem_image.mp b.2
      dsimp only at hab
      rw [← hpa, ← hpb] at hab
      have hthird := congrArg (fun t => (t.1 : ℕ)) hab
      have hfirst := congrArg (fun t => (t.2 : ℕ)) hab
      dsimp only [phi] at hthird hfirst
      have hpval : pa.1 = pb.1 := by
        apply Prod.ext <;> omega
      have hp : pa = pb := Subtype.ext hpval
      apply Subtype.ext
      rw [← hpa, ← hpb, hp]
    · intro a b c hab hbc hca
      obtain ⟨pa, hpaP, hpa⟩ := Finset.mem_image.mp a.2
      obtain ⟨pb, hpbP, hpb⟩ := Finset.mem_image.mp b.2
      obtain ⟨pc, hpcP, hpc⟩ := Finset.mem_image.mp c.2
      rw [← hpa, ← hpb] at hab
      rw [← hpb, ← hpc] at hbc
      rw [← hpc, ← hpa] at hca
      have hab' := congrArg Fin.val hab
      have hbc' := congrArg Fin.val hbc
      have hca' := congrArg Fin.val hca
      dsimp only [phi] at hab' hbc' hca'
      have hsA : pa.1.2 ∈ S := (Finset.mem_product.mp pa.2).2
      have hsB : pb.1.2 ∈ S := (Finset.mem_product.mp pb.2).2
      have hsC : pc.1.2 ∈ S := (Finset.mem_product.mp pc.2).2
      have hAP : pa.1.2 + pb.1.2 = 2 * pc.1.2 := by omega
      have hsEq : pa.1.2 = pb.1.2 := by
        have hfun := mme_3AP_free_no_collision S hSfree
          (fun _ : Fin 1 => pa.1.2)
          (fun _ : Fin 1 => pc.1.2)
          (fun _ : Fin 1 => pb.1.2)
          (fun _ => hsA) (fun _ => hsC) (fun _ => hsB)
          (fun _ => hAP)
        exact congrFun hfun 0
      have hpabval : pa.1 = pb.1 := by
        apply Prod.ext <;> omega
      have hpbcval : pb.1 = pc.1 := by
        apply Prod.ext <;> omega
      have hpab : pa = pb := Subtype.ext hpabval
      have hpbc : pb = pc := Subtype.ext hpbcval
      constructor
      · apply Subtype.ext
        rw [← hpa, ← hpb, hpab]
      · apply Subtype.ext
        rw [← hpb, ← hpc, hpbc]
    · rw [hcardE, Nat.cast_mul]
      calc
        ((H : ℝ) ^ 2) *
              Real.exp (-100 *
                Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
            ≤ (R : ℝ) * (M : ℝ) *
                Real.exp (-4 * Real.sqrt (Real.log M)) := by
              simpa only [M, R] using
                mme_MM_behrend_rate_bound_large H hlarge
        _ = (R : ℝ) *
              ((M : ℝ) * Real.exp (-4 * Real.sqrt (Real.log M))) := by
              ring
        _ ≤ (R : ℝ) * (S.card : ℝ) :=
              mul_le_mul_of_nonneg_left hScard (Nat.cast_nonneg R)
  · have hsmall : H < 4 := by omega
    let z : Fin H := ⟨0, hH⟩
    let E : Finset (Fin H × Fin H × Fin H) := {(z, z, z)}
    have hsubsingleton : ∀ a b : E, a = b := by
      intro a b
      apply Subtype.ext
      have ha : a.1 = (z, z, z) := by
        simpa only [E, Finset.mem_singleton] using a.2
      have hb : b.1 = (z, z, z) := by
        simpa only [E, Finset.mem_singleton] using b.2
      exact ha.trans hb.symm
    refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b _
      exact hsubsingleton a b
    · intro a b _
      exact hsubsingleton a b
    · intro a b _
      exact hsubsingleton a b
    · intro a b c _ _ _
      exact ⟨hsubsingleton a b, hsubsingleton b c⟩
    · simpa only [E, Finset.card_singleton, Nat.cast_one] using
        mme_MM_behrend_rate_bound_small H hH hsmall
