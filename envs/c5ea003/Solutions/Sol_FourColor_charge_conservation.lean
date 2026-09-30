-- Prove2me | solution 1 for FourColor.charge_conservation
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-30T00:06:52.830875+00:00
-- url     : https://prove2.me/submissions/51c98417-05da-4a81-abd2-3c3f5ad8a53a

import Definitions.Def_FourColor_Discharging
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
Euler charge conservation, including empty and disconnected hypermaps and arbitrary rational
transfers. Source: Gonthier (2005), Section 3, PDF p. 9, and Section 5.5, PDF p. 45,
the unnumbered conservation formula for δ(r); pinned Rocq `discharge.v`, lines 167–172
and 201–216. The rational charge 60 − 10δ is a source-derived generalization.
-/

open scoped BigOperators

namespace FourColor.ChargeProof

private noncomputable def cycleDarts {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (p.SameCycle x)

private theorem mem_cycleDarts {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x y : α) : y ∈ cycleDarts p x ↔ p.SameCycle x y := by
  classical
  simp [cycleDarts]

private theorem cycleDarts_card_pos {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) : 0 < (cycleDarts p x).card := by
  exact Finset.card_pos.mpr ⟨x, (mem_cycleDarts p x x).mpr (.refl p x)⟩

private theorem cycleDarts_eq {α : Type*} [Fintype α]
    {p : Equiv.Perm α} {x y : α} (h : p.SameCycle x y) :
    cycleDarts p x = cycleDarts p y := by
  ext z
  rw [mem_cycleDarts, mem_cycleDarts]
  exact ⟨fun hz ↦ h.symm.trans hz, fun hz ↦ h.trans hz⟩

private noncomputable def cycleFiber {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (q : Quotient (Equiv.Perm.SameCycle.setoid p)) : Finset α := by
  classical
  exact Finset.univ.filter (fun y ↦ Quotient.mk _ y = q)

private theorem quotient_fiber {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) :
    cycleFiber p (Quotient.mk _ x) = cycleDarts p x := by
  classical
  ext y
  simp only [cycleFiber, Finset.mem_filter, Finset.mem_univ, true_and, mem_cycleDarts,
    Quotient.eq_iff_equiv]
  exact Equiv.Perm.sameCycle_comm

private theorem sum_inv_cycleDarts_card {α : Type*} [Fintype α] (p : Equiv.Perm α) :
    (∑ x : α, (1 : ℚ) / (cycleDarts p x).card) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) := by
  classical
  letI := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))
  rw [← Finset.sum_fiberwise Finset.univ
    (Quotient.mk (Equiv.Perm.SameCycle.setoid p))]
  have hterm : ∀ q : Quotient (Equiv.Perm.SameCycle.setoid p),
      (∑ y ∈ cycleFiber p q,
        (1 : ℚ) / (cycleDarts p y).card) = 1 := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [quotient_fiber]
      calc
        (∑ y ∈ cycleDarts p x, (1 : ℚ) / (cycleDarts p y).card) =
            ∑ _y ∈ cycleDarts p x, (1 : ℚ) / (cycleDarts p x).card := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [cycleDarts_eq ((mem_cycleDarts p x y).mp hy)]
        _ = 1 := by
          have hne : ((cycleDarts p x).card : ℚ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (cycleDarts_card_pos p x).ne'
          simp [Finset.sum_const, nsmul_eq_mul, hne]
  change (∑ q, ∑ y ∈ cycleFiber p q, (1 : ℚ) / (cycleDarts p y).card) = _
  simp_rw [hterm]
  simp [Nat.card_eq_fintype_card]

private theorem sum_cycle_average {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (g : α → ℚ) :
    (∑ x : α, (∑ y ∈ cycleDarts p x, g y) / (cycleDarts p x).card) = ∑ y : α, g y := by
  classical
  letI := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))
  rw [← Finset.sum_fiberwise Finset.univ (Quotient.mk (Equiv.Perm.SameCycle.setoid p))
    (fun x ↦ (∑ y ∈ cycleDarts p x, g y) / (cycleDarts p x).card)]
  rw [← Finset.sum_fiberwise Finset.univ (Quotient.mk (Equiv.Perm.SameCycle.setoid p)) g]
  change (∑ q, ∑ x ∈ cycleFiber p q,
    (∑ y ∈ cycleDarts p x, g y) / (cycleDarts p x).card) =
    ∑ q, ∑ x ∈ cycleFiber p q, g x
  apply Finset.sum_congr rfl
  intro q _hq
  induction q using Quotient.inductionOn with
  | h x =>
    rw [quotient_fiber]
    calc
      (∑ z ∈ cycleDarts p x,
          (∑ y ∈ cycleDarts p z, g y) / (cycleDarts p z).card) =
          ∑ _z ∈ cycleDarts p x,
            (∑ y ∈ cycleDarts p x, g y) / (cycleDarts p x).card := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [cycleDarts_eq ((mem_cycleDarts p x z).mp hz)]
      _ = ∑ y ∈ cycleDarts p x, g y := by
        have hne : ((cycleDarts p x).card : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (cycleDarts_card_pos p x).ne'
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp

private theorem card_eq_cycle_count_mul {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (k : ℕ) (hk : ∀ x, (cycleDarts p x).card = k) :
    Nat.card α = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) * k := by
  classical
  letI := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid p))))
    (f := Quotient.mk (Equiv.Perm.SameCycle.setoid p)) (fun _ _ ↦ Finset.mem_univ _)
  have hterm : ∀ q : Quotient (Equiv.Perm.SameCycle.setoid p), (cycleFiber p q).card = k := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rw [quotient_fiber, hk]
  change (Finset.univ : Finset α).card = ∑ q, (cycleFiber p q).card at hcard
  simp_rw [hterm] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard

private theorem plain_cycle_card {n : ℕ} (H : Hypermap n) (hplain : H.Plain) (x : Fin n) :
    (cycleDarts H.edge x).card = 2 := by
  classical
  have hcycle : ∀ y, H.edge.SameCycle x y ↔ y = x ∨ y = H.edge x := by
    intro y
    constructor
    · intro hxy
      obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
      clear hxy
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg H.edge h)
        · exact Or.inl ((congrArg H.edge h).trans (hplain x).1)
    · rintro (rfl | rfl)
      · exact .refl _ _
      · exact ⟨1, by simp⟩
  have hdarts : cycleDarts H.edge x = {x, H.edge x} := by
    ext y
    simp [mem_cycleDarts, hcycle]
  rw [hdarts, Finset.card_pair]
  exact (hplain x).2.symm

private theorem cubic_cycle_card {n : ℕ} (H : Hypermap n) (hcubic : H.Cubic) (x : Fin n) :
    (cycleDarts H.node x).card = 3 := by
  classical
  have hcard : Nat.card {y : Fin n // H.node.SameCycle x y} = (cycleDarts H.node x).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  rw [← hcard]
  exact hcubic x

private theorem faceDarts_eq {n : ℕ} (H : Hypermap n) (x : Fin n) :
    H.faceDarts x = cycleDarts H.face x := by
  classical
  ext y
  simp [Hypermap.faceDarts, Hypermap.SameFace, mem_cycleDarts]

private theorem faceArity_pos {n : ℕ} (H : Hypermap n) (x : Fin n) :
    0 < H.faceArity x := by
  simpa [Hypermap.faceArity, faceDarts_eq] using cycleDarts_card_pos H.face x

private theorem totalFaceCharge_formula {n : ℕ} (H : Hypermap n) (transfer : Fin n → ℚ) :
    H.totalFaceCharge transfer = 60 * (H.faceCount : ℚ) - 10 * n := by
  classical
  let g : Fin n → ℚ := fun y ↦ transfer (H.edge y) - transfer y
  have hg : (∑ y : Fin n, g y) = 0 := by
    simp only [g, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp H.edge transfer, sub_self]
  have hinv : (∑ x : Fin n, (1 : ℚ) / H.faceArity x) = H.faceCount := by
    simpa [Hypermap.faceCount, Hypermap.faceArity, faceDarts_eq] using
      sum_inv_cycleDarts_card H.face
  have havg : (∑ x : Fin n, (∑ y ∈ H.faceDarts x, g y) / H.faceArity x) = 0 := by
    simpa [Hypermap.faceArity, faceDarts_eq, hg] using sum_cycle_average H.face g
  have hpoint : ∀ x : Fin n, H.faceCharge transfer x / (H.faceArity x : ℚ) =
      60 * ((1 : ℚ) / H.faceArity x) - 10 +
        (∑ y ∈ H.faceDarts x, g y) / H.faceArity x := by
    intro x
    have hne : (H.faceArity x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (faceArity_pos H x).ne'
    unfold Hypermap.faceCharge
    change (60 - 10 * (H.faceArity x : ℚ) + ∑ y ∈ H.faceDarts x, g y) /
      (H.faceArity x : ℚ) = _
    field_simp
  unfold Hypermap.totalFaceCharge
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hinv, havg]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

end FourColor.ChargeProof

open FourColor

/-- The Euler charge budget and positive-face conclusion for arbitrary rational transfers.
Source: Gonthier (2005), Section 3, PDF p. 9; Section 5.5, PDF p. 45,
unnumbered δ(r) conservation formula; pinned Rocq `discharge.v`, lines 167–172 and
201–216. This is the source-derived rational-transfer formulation. -/
theorem solution :
    ∀ (n : ℕ) (H : Hypermap n), H.Planar → H.Plain → H.Cubic →
      ∀ transfer : Fin n → ℚ,
        H.totalFaceCharge transfer = 120 * (H.componentCount : ℚ) ∧
          (H.Connected → ∃ x : Fin n, 0 < H.faceCharge transfer x) := by
  intro n H hplanar hplain hcubic transfer
  classical
  have he : (n : ℚ) = (H.edgeCount : ℚ) * 2 := by
    have h := ChargeProof.card_eq_cycle_count_mul H.edge 2
      (ChargeProof.plain_cycle_card H hplain)
    simpa [Hypermap.edgeCount] using congrArg (fun k : ℕ ↦ (k : ℚ)) h
  have hn : (n : ℚ) = (H.nodeCount : ℚ) * 3 := by
    have h := ChargeProof.card_eq_cycle_count_mul H.node 3
      (ChargeProof.cubic_cycle_card H hcubic)
    simpa [Hypermap.nodeCount] using congrArg (fun k : ℕ ↦ (k : ℚ)) h
  have hp : (H.edgeCount : ℚ) + H.nodeCount + H.faceCount = n + 2 * H.componentCount := by
    exact_mod_cast hplanar
  have htotal : H.totalFaceCharge transfer = 120 * (H.componentCount : ℚ) := by
    rw [ChargeProof.totalFaceCharge_formula]
    linarith
  refine ⟨htotal, ?_⟩
  intro hconnected
  by_contra hpositive
  push Not at hpositive
  have hnonpos : H.totalFaceCharge transfer ≤ 0 := by
    apply Finset.sum_nonpos
    intro x _hx
    exact div_nonpos_of_nonpos_of_nonneg (hpositive x) (Nat.cast_nonneg _)
  rw [htotal, hconnected] at hnonpos
  norm_num at hnonpos
