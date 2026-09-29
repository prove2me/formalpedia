-- Prove2me | solution 1 for mme_dwz_table2_matchable_outer_family_component_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T18:37:15.944595+00:00
-- url     : https://prove2.me/submissions/c8854f2f-2f82-428c-ae1f-4d6f4921337d

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem component_z_pushforward (k : Fin 5) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
        MME.DWZTable2Counts.component s.1) =
      MME.DWZTable2Counts.alphaZ k := by
  fin_cases k <;> decide

private theorem shape_eq_of_shapeX_shapeZ_eq {s t : Fin 15}
    (hx : MME.DWZSquare.shapeX s = MME.DWZSquare.shapeX t)
    (hz : MME.DWZSquare.shapeZ s = MME.DWZSquare.shapeZ t) :
    s = t := by
  fin_cases s <;> fin_cases t <;>
    simp_all [MME.DWZSquare.shapeX, MME.DWZSquare.shapeZ]

theorem solution (m : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let Outer :=
        {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s,
            Fintype.card {t // w t = s} =
              MME.DWZTable2Counts.component s * m}
      (∀ k,
          Fintype.card {t // K t = k} =
            MME.DWZTable2Counts.alphaZ k * m) ∧
      Nonempty Outer ∧
      (∀ I : Outer, ∀ s,
          Fintype.card {t // I.1 t = s} =
            MME.DWZTable2Counts.component s * m) ∧
      (∀ I : Outer, ∀ t,
          MME.DWZSquare.shapeZ (I.1 t) = K t) ∧
      Function.Injective
        (fun I : Outer => fun t => MME.DWZSquare.shapeX (I.1 t)) ∧
      Nat.card Outer =
        ∏ k : Fin 5,
          Nat.multinomial Finset.univ
            (fun s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k} =>
              MME.DWZTable2Counts.component s.1 * m) ∧
      Nat.multinomial Finset.univ
          (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
        Nat.multinomial Finset.univ
            (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) *
          Nat.card Outer := by
  classical
  let beta :=
    Σ k : Fin 5, Fin (MME.DWZTable2Counts.alphaZ k * m)
  have halpha_sum :
      (∑ k : Fin 5, MME.DWZTable2Counts.alphaZ k) =
        MME.DWZTable2Counts.scale :=
    mme_dwz_table2_integer_counts_exact.2.2.2.2.2.1
  have hcard_beta :
      Fintype.card beta = MME.DWZTable2Counts.scale * m := by
    simp only [beta, Fintype.card_sigma, Fintype.card_fin]
    rw [← Finset.sum_mul, halpha_sum]
  let e : Fin (MME.DWZTable2Counts.scale * m) ≃ beta :=
    Fintype.equivOfCardEq (by simpa using hcard_beta.symm)
  let K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 :=
    fun t => (e t).1
  have hK (k : Fin 5) :
      Fintype.card {t // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m := by
    let eFiber : {t // K t = k} ≃ {b : beta // b.1 = k} :=
      Equiv.subtypeEquiv e (fun _ => by rfl)
    calc
      Fintype.card {t // K t = k} =
          Fintype.card {b : beta // b.1 = k} :=
        Fintype.card_congr eFiber
      _ = Fintype.card (Fin (MME.DWZTable2Counts.alphaZ k * m)) :=
        Fintype.card_congr (Equiv.sigmaSubtype k)
      _ = MME.DWZTable2Counts.alphaZ k * m := Fintype.card_fin _
  have hpush (k : Fin 5) :
      (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
          MME.DWZTable2Counts.component s.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    rw [← Finset.sum_mul, component_z_pushforward]
  let Outer :=
    {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s,
        Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m}
  have hcount :=
    mme_dwz_lemma6_7_typical_denominator_count
      MME.DWZSquare.shapeZ K
      (fun s => MME.DWZTable2Counts.component s * m)
      (fun k => MME.DWZTable2Counts.alphaZ k * m)
      hK hpush
  have hcard :
      Nat.card Outer =
        ∏ k : Fin 5,
          Nat.multinomial Finset.univ
            (fun s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k} =>
              MME.DWZTable2Counts.component s.1 * m) := by
    simpa only [Outer] using hcount.1
  have hcard_pos : 0 < Nat.card Outer := by
    rw [hcard]
    exact Finset.prod_pos fun _ _ => Nat.multinomial_pos _ _
  have hnonempty : Nonempty Outer :=
    (Finite.card_pos_iff.mp hcard_pos)
  have hshape :
      ∀ I : Outer, ∀ s,
        Fintype.card {t // I.1 t = s} =
          MME.DWZTable2Counts.component s * m :=
    fun I s => I.2.2 s
  have hmatch :
      ∀ I : Outer, ∀ t,
        MME.DWZSquare.shapeZ (I.1 t) = K t :=
    fun I t => I.2.1 t
  have hinjective :
      Function.Injective
        (fun I : Outer => fun t => MME.DWZSquare.shapeX (I.1 t)) := by
    intro I J hIJ
    apply Subtype.ext
    funext t
    apply shape_eq_of_shapeX_shapeZ_eq
    · exact congrFun hIJ t
    · rw [I.2.1 t, J.2.1 t]
  refine ⟨K, hK, hnonempty, hshape, hmatch, hinjective, hcard, ?_⟩
  simpa only [Outer] using hcount.2
