-- Prove2me | Definitions.Def_mme_kronFin_rec_group_position_equiv_data
-- name    : mme_kronFin_rec_group_position_equiv_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:32:56.729812+00:00
-- url     : https://prove2.me/theorems/21cc09ab-fd84-44a9-b1dd-49b5326a25c1
-- title:
--   Exact coordinates for consecutive Kronecker fiber grouping
-- statement:
--   For a finite family of fiber sizes $(c_s)_{s<k}$, this module constructs the exact equivalence between positions of the recursion-aligned flattened family and dependent pairs $(s,r)$ with $r<c_s$. It also proves that the flattened family entry at a position is precisely the entry indexed by the corresponding fiber label. This coordinate interface lets the DWZ source order be permuted into the fifteen consecutive Table-2 component powers without losing literal basis-word identities.
-- source:
--   Du–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Table 2 and the regrouping used in Section 6; formal coordinate infrastructure for the Prove2Me 2.3747 mission.

import Definitions.Def_mme_kronFin_rec_groups_data

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.TensorObj

/-- Read a recursion-aligned concatenated position as a left or right
position. -/
def recAppendPositionTo : ∀ (m n : ℕ),
    Fin (recAppendLength m n) → Fin m ⊕ Fin n
  | 0, _, r => Sum.inr r
  | m + 1, n, r =>
      Fin.cases (Sum.inl 0)
        (fun q => match recAppendPositionTo m n q with
          | Sum.inl a => Sum.inl a.succ
          | Sum.inr b => Sum.inr b) r

/-- Reassemble a left or right position into the recursion-aligned
concatenation. -/
def recAppendPositionFrom : ∀ (m n : ℕ),
    Fin m ⊕ Fin n → Fin (recAppendLength m n)
  | 0, _, Sum.inl a => a.elim0
  | 0, _, Sum.inr b => b
  | m + 1, n, Sum.inl a =>
      Fin.cases ⟨0, Nat.zero_lt_succ _⟩
        (fun q => (recAppendPositionFrom m n (Sum.inl q)).succ) a
  | m + 1, n, Sum.inr b =>
      (recAppendPositionFrom m n (Sum.inr b)).succ

theorem recAppendPositionTo_from : ∀ (m n : ℕ)
    (x : Fin m ⊕ Fin n),
    recAppendPositionTo m n (recAppendPositionFrom m n x) = x
  | 0, _, Sum.inl a => a.elim0
  | 0, _, Sum.inr _ => rfl
  | m + 1, n, Sum.inl a => by
      refine Fin.cases ?_ (fun q => ?_) a
      · change Sum.inl (⟨0, _⟩ : Fin (m + 1)) = Sum.inl 0
        exact congrArg Sum.inl (Fin.ext rfl)
      · simp only [recAppendPositionFrom, recAppendPositionTo,
          Fin.cases_succ]
        rw [recAppendPositionTo_from m n (Sum.inl q)]
  | m + 1, n, Sum.inr b => by
      simp only [recAppendPositionFrom, recAppendPositionTo,
        Fin.cases_succ]
      rw [recAppendPositionTo_from m n (Sum.inr b)]

theorem recAppendPositionFrom_to : ∀ (m n : ℕ)
    (r : Fin (recAppendLength m n)),
    recAppendPositionFrom m n (recAppendPositionTo m n r) = r
  | 0, _, _ => rfl
  | m + 1, n, r => by
      refine Fin.cases ?_ (fun q => ?_) r
      · apply Fin.ext
        rfl
      · have ih := recAppendPositionFrom_to m n q
        cases h : recAppendPositionTo m n q with
        | inl a =>
            simpa only [recAppendPositionTo, recAppendPositionFrom,
              Fin.cases_succ, h] using congrArg Fin.succ ih
        | inr b =>
            simpa only [recAppendPositionTo, recAppendPositionFrom,
              Fin.cases_succ, h] using congrArg Fin.succ ih

/-- Exact position equivalence for recursion-aligned concatenation. -/
def recAppendPositionEquiv (m n : ℕ) :
    Fin (recAppendLength m n) ≃ Fin m ⊕ Fin n where
  toFun := recAppendPositionTo m n
  invFun := recAppendPositionFrom m n
  left_inv := recAppendPositionFrom_to m n
  right_inv := recAppendPositionTo_from m n

/-- The concatenated family is literally selected by the corresponding
left/right position. -/
theorem recAppendFamily_at_position
    {alpha : Type u} : ∀ (m n : ℕ) (A : Fin m → alpha)
      (B : Fin n → alpha) (r : Fin (recAppendLength m n)),
      recAppendFamily m n A B r =
        Sum.elim A B (recAppendPositionTo m n r)
  | 0, _, _, _, _ => rfl
  | m + 1, n, A, B, r => by
      refine Fin.cases ?_ (fun q => ?_) r
      · rfl
      · have ih := recAppendFamily_at_position m n
          (fun a : Fin m => A a.succ) B q
        cases h : recAppendPositionTo m n q with
        | inl a =>
            simpa only [recAppendFamily, recAppendPositionTo,
              Fin.cases_succ, h, Sum.elim_inl] using ih
        | inr b =>
            simpa only [recAppendFamily, recAppendPositionTo,
              Fin.cases_succ, h, Sum.elim_inr] using ih

/-- Add the head fiber to a dependent sigma of tail fibers. -/
def sigmaFinSuccEquiv {k : ℕ} (count : Fin (k + 1) → ℕ) :
    Fin (count 0) ⊕ (Σ s : Fin k, Fin (count s.succ)) ≃
      (Σ s : Fin (k + 1), Fin (count s)) where
  toFun
    | Sum.inl r => ⟨0, r⟩
    | Sum.inr p => ⟨p.1.succ, p.2⟩
  invFun p := Fin.cases (fun r => Sum.inl r)
    (fun s r => Sum.inr ⟨s, r⟩) p.1 p.2
  left_inv x := by
    rcases x with r | p
    · rfl
    · rcases p with ⟨s, r⟩
      rfl
  right_inv p := by
    rcases p with ⟨s, r⟩
    cases s using Fin.cases with
    | zero => rfl
    | succ q => rfl

/-- Enumerate all consecutive group positions by their group label and
local position. -/
noncomputable def recGroupPositionEquiv : ∀ (k : ℕ)
    (count : Fin k → ℕ),
    Fin (recGroupLength k count) ≃ (Σ s, Fin (count s))
  | 0, _ =>
      { toFun := fun r => r.elim0
        invFun := fun p => p.1.elim0
        left_inv := fun r => r.elim0
        right_inv := fun p => p.1.elim0 }
  | k + 1, count =>
      (recAppendPositionEquiv (count 0)
        (recGroupLength k (fun s => count s.succ))).trans
      ((Equiv.sumCongr (Equiv.refl _)
        (recGroupPositionEquiv k (fun s => count s.succ))).trans
      (sigmaFinSuccEquiv count))

/-- The group label returned by the position equivalence is exactly the
factor selected by `recGroupFamily`. -/
theorem recGroupFamily_at_position
    {alpha : Type u} : ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → alpha) (r : Fin (recGroupLength k count)),
      recGroupFamily k count X r = X (recGroupPositionEquiv k count r).1
  | 0, _, _, r => r.elim0
  | k + 1, count, X, r => by
      change recAppendFamily (count 0)
          (recGroupLength k (fun s => count s.succ))
          (fun _ => X 0)
          (recGroupFamily k (fun s => count s.succ)
            (fun s => X s.succ)) r = _
      rw [recAppendFamily_at_position]
      cases h : recAppendPositionTo (count 0)
          (recGroupLength k (fun s => count s.succ)) r with
      | inl a =>
          rw [Sum.elim_inl]
          have hpos :
              (recGroupPositionEquiv (k + 1) count r).1 = 0 := by
            unfold recGroupPositionEquiv
            change (sigmaFinSuccEquiv count
              ((Equiv.sumCongr (Equiv.refl _)
                (recGroupPositionEquiv k (fun s => count s.succ)))
                (recAppendPositionTo (count 0)
                  (recGroupLength k (fun s => count s.succ)) r))).1 = 0
            rw [h]
            rfl
          rw [hpos]
      | inr b =>
          have ih := recGroupFamily_at_position k
            (fun s => count s.succ) (fun s => X s.succ) b
          rw [Sum.elim_inr]
          have hpos :
              (recGroupPositionEquiv (k + 1) count r).1 =
                (recGroupPositionEquiv k
                  (fun s => count s.succ) b).1.succ := by
            change (sigmaFinSuccEquiv count
              ((Equiv.sumCongr (Equiv.refl _)
                (recGroupPositionEquiv k (fun s => count s.succ)))
                (recAppendPositionTo (count 0)
                  (recGroupLength k (fun s => count s.succ)) r))).1 =
              (recGroupPositionEquiv k
                (fun s => count s.succ) b).1.succ
            rw [h]
            change (sigmaFinSuccEquiv count
              (Sum.inr (recGroupPositionEquiv k
                (fun s => count s.succ) b))).1 = _
            change (recGroupPositionEquiv k
              (fun s => count s.succ) b).1.succ = _
            exact rfl
          rw [hpos]
          exact ih

end MME.TensorObj


