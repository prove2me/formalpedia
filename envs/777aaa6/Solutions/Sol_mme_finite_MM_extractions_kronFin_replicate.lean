-- Prove2me | solution 1 for mme_finite_MM_extractions_kronFin_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:12:14.530171+00:00
-- url     : https://prove2.me/submissions/f761c929-aa44-45f3-9f3a-51d2fe324002

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

namespace FiniteMMKronReplicate

private theorem strassen_fin_sum_mono
    {R : Type*} [CommSemiring R] (P : StrassenPreorder R) :
    ∀ (n : ℕ) (f g : Fin n → R),
      (∀ i, P.le (f i) (g i)) →
      P.le (∑ i, f i) (∑ i, g i) := by
  intro n
  induction n with
  | zero =>
      intro f g h
      simp only [Fin.sum_univ_zero]
      exact P.le_refl 0
  | succ n ih =>
      intro f g h
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 := h 0
      have ht := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
      exact P.le_trans _ _ _
        (P.add_right _ _ h0 (∑ i : Fin n, f i.succ))
        (by
          simpa [add_comm] using
            P.add_right _ _ ht (g 0))

private theorem strassen_fin_prod_mono
    {R : Type*} [CommSemiring R] (P : StrassenPreorder R) :
    ∀ (n : ℕ) (f g : Fin n → R),
      (∀ i, P.le (f i) (g i)) →
      P.le (∏ i, f i) (∏ i, g i) := by
  intro n
  induction n with
  | zero =>
      intro f g h
      simp only [Fin.prod_univ_zero]
      exact P.le_refl 1
  | succ n ih =>
      intro f g h
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have h0 := h 0
      have ht := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
      exact P.le_trans _ _ _
        (P.mul_right _ _ h0 (∏ i : Fin n, f i.succ))
        (by
          simpa [mul_comm] using
            P.mul_right _ _ ht (g 0))

end FiniteMMKronReplicate

theorem solution
    {K : Type u} [Field K]
    {n W V : ℕ} (Y : Fin n → TensorObj K 3)
    (L : ℝ) (hn : 0 < n) (hL : 0 ≤ L)
    (hextract : ∀ p : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          (Y p) ∧
        L ≤ (k : ℝ) ∧
        (∀ i, a i * b i * c i = V)) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        (TensorObj.bigAdd (fun _ : Fin W => TensorObj.kronFin n Y)) ∧
      (W : ℝ) * L ^ n ≤ (k : ℝ) ∧
      (∀ i, a i * b i * c i = V ^ n) := by
  classical
  choose k a b c hrestrict hk hvolume using hextract
  let S := ∀ p : Fin n, Fin (k p)
  let J := Fin W × S
  let N : ℕ := Fintype.card J
  let e : Fin N ≃ J := (Fintype.equivFin J).symm
  let aa : Fin N → ℕ := fun j => ∏ p, a p ((e j).2 p)
  let bb : Fin N → ℕ := fun j => ∏ p, b p ((e j).2 p)
  let cc : Fin N → ℕ := fun j => ∏ p, c p ((e j).2 p)
  refine ⟨N, aa, bb, cc, ?_, ?_, ?_⟩
  · let P := TensorQ.tensorStrassen K 3 (by omega)
    let E : Fin n → TensorObj K 3 := fun p =>
      TensorObj.bigAdd (fun i => MMObj K (a p i) (b p i) (c p i))
    have hpoint : ∀ p : Fin n,
        P.le (TensorQ.toQ (E p)) (TensorQ.toQ (Y p)) := by
      intro p
      exact (TensorQ.le_toQ (E p) (Y p)).mpr (hrestrict p)
    have hprod :
        P.le (∏ p, TensorQ.toQ (E p))
          (∏ p, TensorQ.toQ (Y p)) :=
      FiniteMMKronReplicate.strassen_fin_prod_mono P n
        (fun p => TensorQ.toQ (E p)) (fun p => TensorQ.toQ (Y p)) hpoint
    have hsum :
        P.le (∑ _w : Fin W, ∏ p, TensorQ.toQ (E p))
          (∑ _w : Fin W, ∏ p, TensorQ.toQ (Y p)) :=
      FiniteMMKronReplicate.strassen_fin_sum_mono P W
        (fun _ => ∏ p, TensorQ.toQ (E p))
        (fun _ => ∏ p, TensorQ.toQ (Y p)) (fun _ => hprod)
    apply (TensorQ.le_toQ _ _).mp
    change P.le _ _
    have hleft :
        TensorQ.toQ
            (TensorObj.bigAdd (fun i => MMObj K (aa i) (bb i) (cc i))) =
          ∑ _w : Fin W, ∏ p, TensorQ.toQ (E p) := by
      rw [TensorQ.toQ_bigAdd]
      calc
        (∑ j : Fin N, TensorQ.toQ (MMObj K (aa j) (bb j) (cc j))) =
            ∑ q : J,
              TensorQ.toQ
                (MMObj K
                  (∏ p, a p (q.2 p))
                  (∏ p, b p (q.2 p))
                  (∏ p, c p (q.2 p))) := by
          apply Fintype.sum_equiv e
          intro j
          simp only [aa, bb, cc, Equiv.apply_symm_apply]
        _ = ∑ q : J,
              ∏ p, TensorQ.toQ
                (MMObj K (a p (q.2 p)) (b p (q.2 p)) (c p (q.2 p))) := by
          apply Finset.sum_congr rfl
          intro q hq
          have hmm := mme_kronFin_MMObj_iso (K := K) n
            (fun p => a p (q.2 p))
            (fun p => b p (q.2 p))
            (fun p => c p (q.2 p))
          calc
            TensorQ.toQ
                (MMObj K
                  (∏ p, a p (q.2 p))
                  (∏ p, b p (q.2 p))
                  (∏ p, c p (q.2 p))) =
                TensorQ.toQ
                  (TensorObj.kronFin n (fun p =>
                    MMObj K (a p (q.2 p)) (b p (q.2 p)) (c p (q.2 p)))) :=
              TensorQ.toQ_eq_iff.mpr hmm.symm
            _ = ∏ p, TensorQ.toQ
                  (MMObj K (a p (q.2 p)) (b p (q.2 p)) (c p (q.2 p))) :=
              mme_toQ_kronFin _
        _ = ∑ _w : Fin W, ∑ s : S,
              ∏ p, TensorQ.toQ
                (MMObj K (a p (s p)) (b p (s p)) (c p (s p))) := by
          rw [Fintype.sum_prod_type]
        _ = ∑ _w : Fin W, ∏ p, ∑ i : Fin (k p),
              TensorQ.toQ (MMObj K (a p i) (b p i) (c p i)) := by
          apply Finset.sum_congr rfl
          intro w hw
          exact (Fintype.prod_sum
            (fun p i => TensorQ.toQ (MMObj K (a p i) (b p i) (c p i)))).symm
        _ = ∑ _w : Fin W, ∏ p, TensorQ.toQ (E p) := by
          congr 1
          funext w
          congr 1
          funext p
          exact (TensorQ.toQ_bigAdd
            (fun i => MMObj K (a p i) (b p i) (c p i))).symm
    have hright :
        TensorQ.toQ
            (TensorObj.bigAdd (fun _ : Fin W => TensorObj.kronFin n Y)) =
          ∑ _w : Fin W, ∏ p, TensorQ.toQ (Y p) := by
      rw [TensorQ.toQ_bigAdd]
      congr 1
      funext w
      exact mme_toQ_kronFin _
    rw [hleft, hright]
    exact hsum
  · have hprodK : L ^ n ≤ ∏ p, (k p : ℝ) := by
      calc
        L ^ n = ∏ _p : Fin n, L := by simp
        _ ≤ ∏ p, (k p : ℝ) := by
          exact Finset.prod_le_prod (fun _ _ => hL) (fun p _ => hk p)
    have hmul := mul_le_mul_of_nonneg_left hprodK (by positivity : (0 : ℝ) ≤ W)
    have hcardN : N = W * ∏ p, k p := by
      dsimp [N, J, S]
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
      simp
    rw [hcardN]
    push_cast
    exact hmul
  · intro j
    dsimp [aa, bb, cc]
    calc
      (∏ p, a p ((e j).2 p)) *
            (∏ p, b p ((e j).2 p)) *
            (∏ p, c p ((e j).2 p)) =
          ∏ p, (a p ((e j).2 p) * b p ((e j).2 p) * c p ((e j).2 p)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ = ∏ _p : Fin n, V := by
        apply Finset.prod_congr rfl
        intro p hp
        exact hvolume p ((e j).2 p)
      _ = V ^ n := by simp
