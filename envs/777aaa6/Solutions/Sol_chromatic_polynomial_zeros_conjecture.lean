-- Prove2me | solution 1 for chromatic_polynomial_zeros_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:39.600509+00:00
-- url     : https://prove2.me/submissions/334e3acd-3817-432c-a824-0792fb2222e4

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

namespace ChromaticCounting

private instance finiteSetoid (n : ℕ) : Finite (Setoid (Fin n)) :=
  Finite.of_injective (fun s : Setoid (Fin n) => s.r) (by
    intro s t h
    exact Setoid.ext (fun _ _ => Iff.of_eq (congrFun (congrFun h _) _)))

private def Partition {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {s : Setoid (Fin n) // ∀ v w, G.Adj v w → ¬ s v w}

private def Coloring {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :=
  {f : Fin n → Fin k // ∀ v w, G.Adj v w → f v ≠ f w}

private noncomputable instance partitionFintype {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype (Partition G) := by
  unfold Partition
  exact Fintype.ofFinite _

private noncomputable instance coloringFintype {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Fintype (Coloring G k) := by
  unfold Coloring
  exact Fintype.ofFinite _

private def colorPartition {n k : ℕ} {G : SimpleGraph (Fin n)}
    (f : Coloring G k) : Partition G := ⟨Setoid.ker f.val, f.property⟩

private def labelPartition {n k : ℕ} {G : SimpleGraph (Fin n)} (s : Partition G)
    (e : Quotient s.val ↪ Fin k) : {f : Coloring G k // colorPartition f = s} := by
  refine ⟨⟨fun v => e ⟦v⟧, ?_⟩, ?_⟩
  · intro v w hvw h
    exact s.property v w hvw (Quotient.exact (e.injective h))
  · apply Subtype.ext
    apply Setoid.ext
    intro v w
    exact ⟨fun h => Quotient.exact (e.injective h),
      fun h => congrArg e (Quotient.sound h)⟩

private theorem labelPartition_bijective {n k : ℕ} {G : SimpleGraph (Fin n)}
    (s : Partition G) : Function.Bijective (labelPartition (k := k) s) := by
  constructor
  · intro e f h
    apply Function.Embedding.ext
    intro q
    induction q using Quotient.inductionOn with
    | h v => exact congrArg (fun p => p.val.val v) h
  · intro p
    have hker : Setoid.ker p.val.val = s.val := congrArg Subtype.val p.property
    let e : Quotient s.val ↪ Fin k :=
      ⟨Quotient.lift p.val.val (by
        intro v w hvw
        change Setoid.ker p.val.val v w
        rw [hker]
        exact hvw), by
        intro q r h
        induction q using Quotient.inductionOn with
        | h v =>
          induction r using Quotient.inductionOn with
          | h w =>
            apply Quotient.sound
            rw [← hker]
            exact h⟩
    refine ⟨e, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem coloring_card {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Fintype.card (Coloring G k) =
      ∑ s : Partition G, k.descFactorial (Nat.card (Quotient s.val)) := by
  classical
  calc
    Fintype.card (Coloring G k) =
        Fintype.card (Σ s : Partition G, {f : Coloring G k // colorPartition f = s}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv colorPartition).symm
    _ = ∑ s : Partition G, Fintype.card {f : Coloring G k // colorPartition f = s} :=
      Fintype.card_sigma
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      letI : Fintype (Quotient s.val) := Fintype.ofFinite _
      rw [← Fintype.card_congr (Equiv.ofBijective _ (labelPartition_bijective (k := k) s))]
      simp [Fintype.card_embedding_eq, Nat.card_eq_fintype_card]

end ChromaticCounting

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ P : Polynomial ℤ, ∀ k : ℤ, 0 ≤ k →
      (P.eval k).toNat = {col : Fin n → Fin k.toNat |
        ∀ v w : Fin n, G.Adj v w → col v ≠ col w}.ncard := by
  classical
  refine ⟨∑ s : ChromaticCounting.Partition G,
    descPochhammer ℤ (Nat.card (Quotient s.val)), ?_⟩
  intro k hk
  have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  rw [← hcast]
  simp only [Polynomial.eval_finset_sum, descPochhammer_eval_eq_descFactorial]
  rw [← Nat.cast_sum, Int.toNat_natCast]
  rw [← ChromaticCounting.coloring_card]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)
