-- Prove2me | solution 1 for lean_workbook_plus_68616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:59:19.649373+00:00
-- url     : https://prove2.me/submissions/812c1ef6-0278-4132-9642-79c73981ffb2

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.ModEq
import Mathlib.SetTheory.Cardinal.Finite

private theorem finite_strictMono_spacing {k : ℕ} (f : Fin k → ℕ)
    (hf : StrictMono f) (i j : Fin k) (hij : i ≤ j) :
    f i + j.val ≤ f j + i.val := by
  have aux : ∀ b, i.val ≤ b → ∀ hb : b < k,
      f i + b ≤ f ⟨b, hb⟩ + i.val := by
    intro b hib
    induction b, hib using Nat.le_induction with
    | base => intro hb; exact le_rfl
    | succ b hib ih =>
      intro hb
      have hb' : b < k := by omega
      have hprev := ih hb'
      have hstep := hf (show (⟨b, hb'⟩ : Fin k) < ⟨b + 1, hb⟩ from by
        change b < b + 1
        omega)
      omega
  exact aux j.val hij j.isLt

private theorem finite_orderEmbedding_bounds {k m : ℕ} (g : Fin k ↪o Fin m)
    (i : Fin k) : i.val ≤ (g i).val ∧ (g i).val + k ≤ m + i.val := by
  have hik := i.isLt
  have hk : 0 < k := by omega
  have hmono : StrictMono (fun j => (g j).val) := Fin.val_strictMono.comp g.strictMono
  have hl := finite_strictMono_spacing _ hmono ⟨0, hk⟩ i (by
    change 0 ≤ i.val
    omega)
  have hu := finite_strictMono_spacing _ hmono i ⟨k - 1, by omega⟩ (by
    change i.val ≤ k - 1
    omega)
  have hlast := (g ⟨k - 1, by omega⟩).isLt
  change (g ⟨0, hk⟩).val + i.val ≤ (g i).val + 0 at hl
  change (g i).val + (k - 1) ≤ (g ⟨k - 1, _⟩).val + i.val at hu
  constructor <;> omega

def AlternatingParitySequence (n k : ℕ) :=
  {a : Fin k → ℕ // StrictMono a ∧
    ∀ i, 1 ≤ a i ∧ a i ≤ n ∧ a i % 2 = (i.val + 1) % 2}

def alternatingParitySequenceEquiv (n k : ℕ) :
    AlternatingParitySequence n k ≃ (Fin k ↪o Fin ((n + k) / 2)) where
  toFun a := OrderEmbedding.ofStrictMono
    (fun i => ⟨(a.val i + i.val) / 2, by
      have hi := a.prop.2 i
      have hik := i.isLt
      omega⟩)
    (by
      intro i j hij
      have ha := a.prop.1 hij
      change (a.val i + i.val) / 2 < (a.val j + j.val) / 2
      have hij' : i.val < j.val := hij
      omega)
  invFun g := ⟨fun i => 2 * (g i).val + 1 - i.val, by
    constructor
    · intro i j hij
      have hi := finite_orderEmbedding_bounds g i
      have hj := finite_orderEmbedding_bounds g j
      have hgap := finite_strictMono_spacing (fun t => (g t).val)
        (Fin.val_strictMono.comp g.strictMono) i j hij.le
      have hij' : i.val < j.val := hij
      change (g i).val + j.val ≤ (g j).val + i.val at hgap
      change 2 * (g i).val + 1 - i.val < 2 * (g j).val + 1 - j.val
      omega
    · intro i
      have hi := finite_orderEmbedding_bounds g i
      have hik := i.isLt
      change 1 ≤ 2 * (g i).val + 1 - i.val ∧
        2 * (g i).val + 1 - i.val ≤ n ∧
        (2 * (g i).val + 1 - i.val) % 2 = (i.val + 1) % 2
      omega⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    change 2 * ((a.val i + i.val) / 2) + 1 - i.val = a.val i
    have hi := a.prop.2 i
    omega
  right_inv g := by
    ext i
    change (2 * (g i).val + 1 - i.val + i.val) / 2 = (g i).val
    have hi := finite_orderEmbedding_bounds g i
    omega

private def finiteOrderEmbeddingSubsetEquiv (k m : ℕ) :
    (Fin k ↪o Fin m) ≃ {s : Finset (Fin m) // s.card = k} where
  toFun g := ⟨Finset.univ.map g.toEmbedding, by simp⟩
  invFun s := s.val.orderEmbOfFin s.prop
  left_inv g := by
    apply DFunLike.ext
    intro i
    have h := Finset.orderEmbOfFin_unique
      (s := Finset.univ.map g.toEmbedding) (by simp :
        (Finset.univ.map g.toEmbedding).card = k)
      (f := g) (fun j => by simp) g.strictMono
    exact congrFun h.symm i
  right_inv s := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ _ _

theorem alternating_parity_sequence_count (n k : ℕ) :
    Nat.card (AlternatingParitySequence n k) = ((n + k) / 2).choose k := by
  rw [Nat.card_congr (alternatingParitySequenceEquiv n k),
    Nat.card_congr (finiteOrderEmbeddingSubsetEquiv k ((n + k) / 2))]
  let e : {s : Finset (Fin ((n + k) / 2)) // s.card = k} ≃
      (Finset.univ.powersetCard k : Finset (Finset (Fin ((n + k) / 2)))) :=
    Equiv.subtypeEquivRight (fun s => by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem solution (n k : ℕ) : n ≥ k → ∃ a : ℕ → ℕ,
    (∀ i : ℕ, 1 ≤ i ∧ i ≤ k → a i ≡ i [ZMOD 2] ∧ a i < a (i + 1)) ∧
      a k ≤ n := by
  intro h
  exact ⟨id, fun i _ => ⟨Int.ModEq.refl _, Nat.lt_succ_self i⟩, h⟩
