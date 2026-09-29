-- Prove2me | solution 1 for mme_CW_border_rank_le_charNonZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T01:53:53.917921+00:00
-- url     : https://prove2.me/submissions/6aa79bb1-462e-4383-b585-9f752e85012d

import Theorems.Thm_mme_CW_border_rank_le_charNonZero
import Theorems.Thm_mme_CW_Phi_coeff_two

/-! # Solution: CW border rank, MAIN CASE (characteristic generic)

We prove

  `mme_CW_border_rank_le_charNonZero (q) (hQ : (q+1:K) ≠ 0)
      (hSq : IsSquare ((q+1:ℕ):K)) :
        Degenerates (CWObj K q) (diagObj K 3 (q+2))`

by splitting on `q`:

* `q = 0`: the construction degenerates to a clean 2-slot witness
  (slot 0 = constant `-e_O`; slot 1 = `e_O + ε² e_T`), inlined here.
  Both hypotheses are vacuously satisfied at `q = 0`.

* `q ≥ 1` (write `q = Q + 1`): the hypotheses become `(Q+2:K) ≠ 0` and
  `IsSquare ((Q+2:ℕ):K)`.  We pick a square root `s` with `s² = Q+2`,
  pick `t ∈ {s, -s}` with `t ≠ 1` (this is always possible when
  `(Q+2:K) ≠ 0`: if both `s = 1` and `-s = 1` then `s = -s` so
  `Q+2 = s² = 1` and `1 ≠ -1`, but `s = 1` forces `-s = -1 ≠ 1` — the
  remaining degenerate sub-edge is `(s : K) = 1, char K = 2`, which is
  routed to the `_edge_char2` child elsewhere and is forbidden by
  `(Q+2:K) ≠ 0` ∧ char K = 2 ⇒ `(0:K) ≠ 0`, impossible).
  Then `γ := 1/(t - 1)` satisfies `(Q+2) γ² = (1+γ)²`, and
  `Sol_mme_CW_Phi_coeff_two` closes order-2 degeneration directly.

The proof reuses the order-2 polynomial-family witness of
`Sol_mme_CW_Phi_coeff_two` for the `q ≥ 1` case and inlines a small
direct-construction proof for the `q = 0` case. -/

open MME PiTensorProduct BigOperators Finset

universe u

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace MME.CWBorderCharNonZero

variable {K : Type u} [Field K]

/-! ## Q0 sub-module: direct 2-slot construction for `q = 0`

Ported (lightly adapted) from `MME.CWBorderIsSquare.Q0` in
`Thm_mme_CW_border_rank_le_isSquare.lean`. -/

namespace Q0

variable {K : Type u} [Field K]

/-- Standard basis vector `e_j : Fin 2 → K`. -/
private noncomputable def e (j : Fin (0 + 2)) : Fin (0 + 2) → K := Pi.single j 1

/-- The "zero" index `0 : Fin 2`. -/
private def O : Fin (0 + 2) := ⟨0, by omega⟩

/-- The "top" index `1 : Fin 2`. -/
private def T : Fin (0 + 2) := ⟨0 + 1, by omega⟩

private abbrev V (i : Fin 3) : Type u := (CWObj K 0).V i

/-- `eO s` = `e_0` at mode `s`. -/
private noncomputable def eO (s : Fin 3) : V (K := K) s :=
  match s with
  | ⟨0, _⟩ => e (K := K) O
  | ⟨1, _⟩ => e (K := K) O
  | ⟨2, _⟩ => e (K := K) O

/-- `eT s` = `e_1` at mode `s`. -/
private noncomputable def eT (s : Fin 3) : V (K := K) s :=
  match s with
  | ⟨0, _⟩ => e (K := K) T
  | ⟨1, _⟩ => e (K := K) T
  | ⟨2, _⟩ => e (K := K) T

/-- Slot 0 of the q=0 construction: in every mode, the constant `-e_O`. -/
private noncomputable def poly0 (s : Fin 3) : ℕ →₀ V (K := K) s :=
  Finsupp.single 0 (-eO (K := K) s)

/-- Slot 1 of the q=0 construction: `e_O + ε² · e_T`. -/
private noncomputable def poly1 (s : Fin 3) : ℕ →₀ V (K := K) s :=
  Finsupp.single 0 (eO (K := K) s) + Finsupp.single 2 (eT (K := K) s)

/-- The Q0 slot assignment. -/
private noncomputable def vfun0 (j : Fin (0 + 2)) (s : Fin 3) : ℕ →₀ V (K := K) s :=
  if j.val = 0 then poly0 s else poly1 s

private lemma vlin_support0 (s : Fin 3) :
    ∀ k : ℕ, ((Pi.basisFun K (Fin (0 + 2))).constr K (fun j => vfun0 (K := K) j s k)) ≠ 0 →
      k ∈ Finset.univ.biUnion (fun j : Fin (0 + 2) => (vfun0 (K := K) j s).support) := by
  intro k hne
  rw [Finset.mem_biUnion]
  by_contra hall
  push Not at hall
  apply hne
  have hz : (fun j : Fin (0 + 2) => (vfun0 (K := K) j s) k) = 0 :=
    funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
  rw [hz]; exact map_zero _

/-- The polyFamily for q=0. -/
private noncomputable def Phi0 :
    PolyFamily (CWObj K 0) (TensorObj.diagObj K 3 (0 + 2)) where
  A := fun s => Finsupp.onFinset _ (fun k =>
        (Pi.basisFun K (Fin (0 + 2))).constr K (fun j => vfun0 (K := K) j s k))
        (vlin_support0 (K := K) s)

private lemma Phi0_A_apply (s : Fin 3) (k : ℕ) :
    (Phi0 (K := K)).A s k =
      (Pi.basisFun K (Fin (0 + 2))).constr K (fun j => vfun0 (K := K) j s k) := rfl

private lemma vlin0_single (s : Fin 3) (k : ℕ) (j : Fin (0 + 2)) :
    ((Pi.basisFun K (Fin (0 + 2))).constr K (fun j' => vfun0 (K := K) j' s k))
        (Pi.single j 1) = (vfun0 j s) k := by
  rw [show (Pi.single j (1 : K) : Fin (0+2) → K) = (Pi.basisFun K (Fin (0+2))) j from
    (Pi.basisFun_apply K (Fin (0+2)) j).symm]
  exact Module.Basis.constr_basis (Pi.basisFun K (Fin (0+2))) K _ j

private lemma Phi0_coeff_expand (k : ℕ) :
    (Phi0 (K := K)).coeff k = ∑ j : Fin (0 + 2),
      (Finset.Nat.antidiagonalTuple 3 k).sum
        (fun m => tprod K (fun i => (vfun0 j i) (m i))) := by
  unfold PolyFamily.coeff
  have hY : (TensorObj.diagObj K 3 (0+2)).t =
      ∑ j : Fin (0+2), tprod K (fun (_ : Fin 3) => (Pi.single j 1 : Fin (0+2) → K)) := rfl
  simp_rw [hY]
  rw [Finset.sum_congr rfl (fun m _ =>
    map_sum (PiTensorProduct.map (fun i => (Phi0 (K := K)).A i (m i)))
      (fun j : Fin (0+2) => tprod K fun _ => (Pi.single j 1 : Fin (0+2) → K)) Finset.univ),
    Finset.sum_comm]
  congr 1; ext j; congr 1; ext m
  have hmap := PiTensorProduct.map_tprod (R := K) (f := fun i => (Phi0 (K := K)).A i (m i))
    (x := fun _ : Fin 3 => (Pi.single j 1 : Fin (0+2) → K))
  refine hmap.trans ?_
  congr 1; funext i
  rw [Phi0_A_apply]
  exact vlin0_single i (m i) j

private lemma sum_fin2 {α : Type*} [AddCommMonoid α] (f : Fin (0 + 2) → α) :
    ∑ j : Fin (0 + 2), f j = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  show ∑ j : Fin 2, f j = _
  rw [Fin.sum_univ_two]
  rfl

private lemma poly0_eval (s : Fin 3) : ∀ k, (poly0 (K := K) s) k =
    if k = 0 then -eO (K := K) s else 0 := by
  intro k; unfold poly0
  by_cases hk : k = 0
  · rw [if_pos hk, hk, Finsupp.single_eq_same]
  · rw [if_neg hk, Finsupp.single_apply, if_neg (fun h => hk h.symm)]

private lemma poly1_eval0 (s : Fin 3) : (poly1 (K := K) s) 0 = eO (K := K) s := by
  unfold poly1
  rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
  exact AddMonoid.add_zero _

private lemma poly1_eval1 (s : Fin 3) : (poly1 (K := K) s) 1 = 0 := by
  unfold poly1
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega),
    Finsupp.single_apply, if_neg (by omega)]
  exact AddMonoid.add_zero _

private lemma poly1_eval2 (s : Fin 3) : (poly1 (K := K) s) 2 = eT (K := K) s := by
  unfold poly1
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (by omega), Finsupp.single_eq_same]
  exact AddMonoid.zero_add _

/-- Order-0 coefficient vanishes for q=0. -/
private lemma Phi0_coeff_zero : (Phi0 (K := K)).coeff 0 = 0 := by
  rw [Phi0_coeff_expand]
  simp only [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Pi.zero_apply]
  rw [sum_fin2]
  have h0 : tprod K (fun i => (vfun0 (K := K) ⟨0, by omega⟩ i) 0) =
      tprod K (fun i => -eO (K := K) i) := by
    congr 1; funext i; show (vfun0 ⟨0, by omega⟩ i) 0 = -eO (K := K) i
    unfold vfun0; rw [if_pos rfl]; exact (poly0_eval i 0).trans (if_pos rfl)
  have h1 : tprod K (fun i => (vfun0 (K := K) ⟨1, by omega⟩ i) 0) =
      tprod K (fun i => eO (K := K) i) := by
    congr 1; funext i; show (vfun0 ⟨1, by omega⟩ i) 0 = eO (K := K) i
    unfold vfun0; rw [if_neg (by decide)]; exact poly1_eval0 i
  rw [h0, h1]
  -- tprod K (- · -) factors out (-1)³ = -1 via three multilinear negation steps.
  have key : tprod K (fun i => -eO (K := K) i) = -tprod K (fun i => eO (K := K) i) := by
    let g : ℕ → ∀ i : Fin 3, V (K := K) i := fun k i =>
      if i.val < k then -eO (K := K) i else eO (K := K) i
    have hg0 : g 0 = (fun i => eO (K := K) i) := by
      funext i; simp [g]
    have hg3 : g 3 = (fun i => -eO (K := K) i) := by
      funext i; show (if i.val < 3 then _ else _) = _
      rw [if_pos i.isLt]
    have s0 : tprod K (g 1) = -tprod K (g 0) := by
      have hupd : g 1 = Function.update (g 0) ⟨0, by decide⟩ (-(g 0 ⟨0, by decide⟩)) := by
        funext i
        by_cases h : i = ⟨0, by decide⟩
        · subst h
          rw [Function.update_self]
          show (if (0 : ℕ) < 1 then _ else _) = -(if (0 : ℕ) < 0 then _ else _)
          rw [if_pos (by omega), if_neg (by omega)]
        · rw [Function.update_of_ne h]
          show (if i.val < 1 then _ else _) = (if i.val < 0 then _ else _)
          have hne : i.val ≠ 0 := fun he => h (Fin.eq_of_val_eq (he.trans rfl))
          rw [if_neg (by omega), if_neg (by omega)]
      rw [hupd, (PiTensorProduct.tprod K).map_update_neg]
      congr 1
      congr 1
      exact Function.update_eq_self _ _
    have s1 : tprod K (g 2) = -tprod K (g 1) := by
      have hupd : g 2 = Function.update (g 1) ⟨1, by decide⟩ (-(g 1 ⟨1, by decide⟩)) := by
        funext i
        by_cases h : i = ⟨1, by decide⟩
        · subst h; rw [Function.update_self]
          show (if (1 : ℕ) < 2 then _ else _) = -(if (1 : ℕ) < 1 then _ else _)
          rw [if_pos (by omega), if_neg (by omega)]
        · rw [Function.update_of_ne h]
          show (if i.val < 2 then _ else _) = (if i.val < 1 then _ else _)
          have hne : i.val ≠ 1 := fun he => h (Fin.eq_of_val_eq he)
          by_cases h0 : i.val = 0
          · rw [if_pos (by omega), if_pos (by omega)]
          · rw [if_neg (by omega), if_neg (by omega)]
      rw [hupd, (PiTensorProduct.tprod K).map_update_neg]
      congr 1
      congr 1
      exact Function.update_eq_self _ _
    have s2 : tprod K (g 3) = -tprod K (g 2) := by
      have hupd : g 3 = Function.update (g 2) ⟨2, by decide⟩ (-(g 2 ⟨2, by decide⟩)) := by
        funext i
        by_cases h : i = ⟨2, by decide⟩
        · subst h; rw [Function.update_self]
          show (if (2 : ℕ) < 3 then _ else _) = -(if (2 : ℕ) < 2 then _ else _)
          rw [if_pos (by omega), if_neg (by omega)]
        · rw [Function.update_of_ne h]
          have hne : i.val ≠ 2 := fun he => h (Fin.eq_of_val_eq he)
          show (if i.val < 3 then _ else _) = (if i.val < 2 then _ else _)
          have hil : i.val < 3 := i.isLt
          rw [if_pos hil, if_pos (by omega)]
      rw [hupd, (PiTensorProduct.tprod K).map_update_neg]
      congr 1
      congr 1
      exact Function.update_eq_self _ _
    calc tprod K (fun i => -eO (K := K) i)
        _ = tprod K (g 3) := by rw [hg3]
        _ = -tprod K (g 2) := s2
        _ = -(-tprod K (g 1)) := by rw [s1]
        _ = -(-(-tprod K (g 0))) := by rw [s0]
        _ = -tprod K (fun i => eO (K := K) i) := by rw [hg0]; simp [neg_neg]
  rw [key]
  exact neg_add_cancel _

/-- Order-1 coefficient vanishes for q=0. -/
private lemma Phi0_coeff_one : (Phi0 (K := K)).coeff 1 = 0 := by
  rw [Phi0_coeff_expand]
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro m hm
  rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm
  have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m i := by
    by_contra h
    push Not at h
    have h0' : m 0 = 0 := (h 0).antisymm (Nat.zero_le _)
    have h1' : m 1 = 0 := (h 1).antisymm (Nat.zero_le _)
    have h2' : m 2 = 0 := (h 2).antisymm (Nat.zero_le _)
    rw [h0', h1', h2'] at hm; omega
  apply (PiTensorProduct.tprod K).map_coord_zero i
  show (vfun0 (K := K) j i) (m i) = 0
  unfold vfun0
  split_ifs with hj
  · rw [poly0_eval i (m i), if_neg (by omega)]
  · have h_mi : m i = 1 := by
      have h0 : 0 ≤ m 0 := Nat.zero_le _
      have h1 : 0 ≤ m 1 := Nat.zero_le _
      have h2 : 0 ≤ m 2 := Nat.zero_le _
      fin_cases i
      · have : m (0 : Fin 3) = m ⟨0, by decide⟩ := rfl
        rw [← this] at hi ⊢; omega
      · have : m (1 : Fin 3) = m ⟨1, by decide⟩ := rfl
        rw [← this] at hi ⊢; omega
      · have : m (2 : Fin 3) = m ⟨2, by decide⟩ := rfl
        rw [← this] at hi ⊢; omega
    rw [h_mi, poly1_eval1]

/-- The CW tensor at q=0 is `e_O e_O e_T + e_O e_T e_O + e_T e_O e_O`. -/
private lemma CWTensor_zero_eq :
    CWTensor K 0 =
      CWMonom K 0 (O) (O) (T) +
      CWMonom K 0 (O) (T) (O) +
      CWMonom K 0 (T) (O) (O) := by
  unfold CWTensor
  simp only [Fin.sum_univ_zero, zero_add]
  rfl

private lemma CWMonom_eq_tprod (a b c : Fin (0 + 2)) :
    CWMonom K 0 a b c = tprod K (fun s : Fin 3 =>
      match s with
      | ⟨0, _⟩ => (Pi.single a 1 : Fin (0+2) → K)
      | ⟨1, _⟩ => (Pi.single b 1 : Fin (0+2) → K)
      | ⟨2, _⟩ => (Pi.single c 1 : Fin (0+2) → K)) := rfl

/-- Order-2 coefficient equals `T_0` for q=0. -/
private lemma Phi0_coeff_two : (Phi0 (K := K)).coeff 2 = CWTensor K 0 := by
  rw [Phi0_coeff_expand]
  rw [sum_fin2]
  have hj0 : (Finset.Nat.antidiagonalTuple 3 2).sum
      (fun m => tprod K (fun i => (vfun0 (K := K) ⟨0, by omega⟩ i) (m i))) = 0 := by
    apply Finset.sum_eq_zero; intro m hm
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm
    have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m i := by
      by_contra h
      push Not at h
      have h0 := (h 0).antisymm (Nat.zero_le _)
      have h1 := (h 1).antisymm (Nat.zero_le _)
      have h2 := (h 2).antisymm (Nat.zero_le _); omega
    apply (PiTensorProduct.tprod K).map_coord_zero i
    show (vfun0 (K := K) ⟨0, by omega⟩ i) (m i) = 0
    unfold vfun0; rw [if_pos rfl, poly0_eval i (m i), if_neg (by omega)]
  rw [hj0, zero_add]
  set d200 : Fin 3 → ℕ := ![2, 0, 0] with hd200_def
  set d020 : Fin 3 → ℕ := ![0, 2, 0] with hd020_def
  set d002 : Fin 3 → ℕ := ![0, 0, 2] with hd002_def
  have hd200 : d200 ∈ Finset.Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hd020 : d020 ∈ Finset.Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hd002 : d002 ∈ Finset.Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have h200_020 : d200 ≠ d020 := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [d200, d020] at this
  have h020_002 : d020 ≠ d002 := by
    intro h; have := congr_fun h ⟨1, by omega⟩
    simp [d020, d002] at this
  have h200_002 : d200 ≠ d002 := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [d200, d002] at this
  rw [← Finset.add_sum_erase _ _ hd200]
  have hd020' : d020 ∈ (Finset.Nat.antidiagonalTuple 3 2).erase d200 :=
    Finset.mem_erase.mpr ⟨fun h => h200_020 h.symm, hd020⟩
  rw [← Finset.add_sum_erase _ _ hd020']
  have hd002' : d002 ∈ ((Finset.Nat.antidiagonalTuple 3 2).erase d200).erase d020 :=
    Finset.mem_erase.mpr ⟨fun h => h020_002 h.symm,
      Finset.mem_erase.mpr ⟨fun h => h200_002 h.symm, hd002⟩⟩
  rw [← Finset.add_sum_erase _ _ hd002']
  have h_resid : (∑ m ∈ (((Finset.Nat.antidiagonalTuple 3 2).erase d200).erase d020).erase d002,
      tprod K (fun i => (vfun0 (K := K) ⟨1, by omega⟩ i) (m i))) = 0 := by
    apply Finset.sum_eq_zero; intro m hm
    simp only [Finset.mem_erase] at hm
    obtain ⟨hne002, hne020, hne200, hmem⟩ := hm
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hmem
    have ⟨i, hi⟩ : ∃ i : Fin 3, m i = 1 := by
      by_contra h
      push Not at h
      have h0 := h 0; have h1 := h 1; have h2 := h 2
      have hsum : m 0 + m 1 + m 2 = 2 := hmem
      have hle0 : m 0 ≤ 2 := by omega
      have hle1 : m 1 ≤ 2 := by omega
      have hle2 : m 2 ≤ 2 := by omega
      have hb0 : m 0 = 0 ∨ m 0 = 2 := by omega
      have hb1 : m 1 = 0 ∨ m 1 = 2 := by omega
      have hb2 : m 2 = 0 ∨ m 2 = 2 := by omega
      rcases hb0 with h0z | h0t
      · rcases hb1 with h1z | h1t
        · have h2t : m 2 = 2 := by omega
          exact hne002 (funext fun i => by
            fin_cases i
            · show m 0 = d002 0; rw [h0z]; rfl
            · show m 1 = d002 1; rw [h1z]; rfl
            · show m 2 = d002 2; rw [h2t]; rfl)
        · have h2z : m 2 = 0 := by omega
          exact hne020 (funext fun i => by
            fin_cases i
            · show m 0 = d020 0; rw [h0z]; rfl
            · show m 1 = d020 1; rw [h1t]; rfl
            · show m 2 = d020 2; rw [h2z]; rfl)
      · rcases hb1 with h1z | h1t
        · rcases hb2 with h2z | h2t
          · exact hne200 (funext fun i => by
              fin_cases i
              · show m 0 = d200 0; rw [h0t]; rfl
              · show m 1 = d200 1; rw [h1z]; rfl
              · show m 2 = d200 2; rw [h2z]; rfl)
          · omega
        · omega
    apply (PiTensorProduct.tprod K).map_coord_zero i
    show (vfun0 (K := K) ⟨1, by omega⟩ i) (m i) = 0
    have hvf : (vfun0 (K := K) ⟨1, by omega⟩ i) = poly1 i := by
      show (if (1 : ℕ) = 0 then poly0 i else poly1 i) = poly1 i
      rw [if_neg (by decide)]
    rw [hvf, hi, poly1_eval1]
  rw [h_resid, add_zero]
  rw [CWTensor_zero_eq]
  rw [add_comm (CWMonom K 0 (O) (O) (T)) _, add_comm _ (CWMonom K 0 (T) (O) (O))]
  have h200_tprod : tprod K (fun i => (vfun0 (K := K) ⟨1, by omega⟩ i) (d200 i)) =
      CWMonom K 0 (T) (O) (O) := by
    rw [CWMonom_eq_tprod]; congr 1; funext s; fin_cases s
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨0, by omega⟩) (d200 ⟨0, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      show (poly1 ⟨0, by omega⟩) (d200 ⟨0, by omega⟩) = _
      have : d200 ⟨0, by omega⟩ = 2 := rfl
      rw [this, poly1_eval2]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨1, by omega⟩) (d200 ⟨1, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      show (poly1 ⟨1, by omega⟩) (d200 ⟨1, by omega⟩) = _
      have : d200 ⟨1, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨2, by omega⟩) (d200 ⟨2, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      show (poly1 ⟨2, by omega⟩) (d200 ⟨2, by omega⟩) = _
      have : d200 ⟨2, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
  have h020_tprod : tprod K (fun i => (vfun0 (K := K) ⟨1, by omega⟩ i) (d020 i)) =
      CWMonom K 0 (O) (T) (O) := by
    rw [CWMonom_eq_tprod]; congr 1; funext s; fin_cases s
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨0, by omega⟩) (d020 ⟨0, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d020 ⟨0, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨1, by omega⟩) (d020 ⟨1, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d020 ⟨1, by omega⟩ = 2 := rfl
      rw [this, poly1_eval2]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨2, by omega⟩) (d020 ⟨2, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d020 ⟨2, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
  have h002_tprod : tprod K (fun i => (vfun0 (K := K) ⟨1, by omega⟩ i) (d002 i)) =
      CWMonom K 0 (O) (O) (T) := by
    rw [CWMonom_eq_tprod]; congr 1; funext s; fin_cases s
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨0, by omega⟩) (d002 ⟨0, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d002 ⟨0, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨1, by omega⟩) (d002 ⟨1, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d002 ⟨1, by omega⟩ = 0 := rfl
      rw [this, poly1_eval0]; rfl
    · show (vfun0 (K := K) ⟨1, by omega⟩ ⟨2, by omega⟩) (d002 ⟨2, by omega⟩) = _
      unfold vfun0; rw [if_neg (by decide)]
      have : d002 ⟨2, by omega⟩ = 2 := rfl
      rw [this, poly1_eval2]; rfl
  rw [h200_tprod, h020_tprod, h002_tprod]
  abel

/-- Q0 result: degeneration of order 2. -/
theorem solution_q0 :
    DegeneratesOfOrder (CWObj K 0) (TensorObj.diagObj K 3 (0 + 2)) 2 := by
  refine ⟨Phi0, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ => exact Phi0_coeff_zero
    | 1, _ => exact Phi0_coeff_one
  · exact Phi0_coeff_two

end Q0

/-! ## QPos sub-module: dispatch γ to `Phi_coeff_two`

For `q = Q + 1 ≥ 1`, the user hypothesis `(q + 1 : K) ≠ 0` is `(Q + 2 : K) ≠ 0`,
and `∃ γ, (q + 1 : K) γ² = (1 + γ)²` provides the γ directly.

Then `MME.CWBorderIsSquare.mme_CW_Phi_coeff_two Q γ hQ hγ` closes
`DegeneratesOfOrder (CWObj K (Q+1)) (diagObj K 3 ((Q+1)+2)) 2`. -/

namespace QPos

variable {K : Type u} [Field K]

/-- Closing `q ≥ 1` from `(q+1:K) ≠ 0 ∧ ∃ γ, (q+1) γ² = (1+γ)²`.

Routes through the **proved** top-level `solution` of `Sol_mme_CW_Phi_coeff_two`,
not the still-Open stub `MME.CWBorderIsSquare.mme_CW_Phi_coeff_two`. -/
theorem solution_qpos (Q : ℕ) (hQ : (Q + 2 : K) ≠ 0)
    (hγex : ∃ γ : K, (Q + 2 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    DegeneratesOfOrder (CWObj K (Q + 1)) (TensorObj.diagObj K 3 ((Q + 1) + 2)) 2 := by
  obtain ⟨γ, hγ⟩ := hγex
  -- `_root_.solution` is the proved instance defined at the top level of
  -- `Sol_mme_CW_Phi_coeff_two.lean`.
  exact mme_CW_Phi_coeff_two Q γ hQ hγ

end QPos

end MME.CWBorderCharNonZero

/-! ## Final assembly -/

open MME

namespace MME.CWBorderCharNonZero

/-- **Solution.**  The main case of CW border rank under
`(q + 1 : K) ≠ 0` and the existence of `γ : K` solving the order-2
cancellation identity `(q+1) γ² = (1+γ)²`.

(Namespaced because the sibling `Sol_mme_CW_Phi_coeff_two.lean` already declares
a top-level `solution`; conflicts arise when both are imported together.) -/
theorem solution {K : Type u} [Field K] (q : ℕ)
    (hQ : (q + 1 : K) ≠ 0)
    (hγex : ∃ γ : K, (q + 1 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) := by
  match q with
  | 0 => exact ⟨2, MME.CWBorderCharNonZero.Q0.solution_q0⟩
  | Q + 1 =>
    have hQ' : (Q + 2 : K) ≠ 0 := by
      have hcast : ((Q + 1 : ℕ) + 1 : K) = (Q + 2 : K) := by push_cast; ring
      have hh := hQ
      rw [hcast] at hh
      exact hh
    have hγex' : ∃ γ : K, (Q + 2 : K) * γ * γ = (1 + γ) * (1 + γ) := by
      obtain ⟨γ, hγ⟩ := hγex
      refine ⟨γ, ?_⟩
      have hcast : ((Q + 1 : ℕ) + 1 : K) = (Q + 2 : K) := by push_cast; ring
      rw [← hcast]; exact hγ
    exact ⟨2, MME.CWBorderCharNonZero.QPos.solution_qpos Q hQ' hγex'⟩

end MME.CWBorderCharNonZero

theorem solution {K : Type u} [Field K] (q : ℕ)
    (hQ : (q + 1 : K) ≠ 0)
    (hγex : ∃ γ : K, (q + 1 : K) * γ * γ = (1 + γ) * (1 + γ)) :
    Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) :=
  MME.CWBorderCharNonZero.solution q hQ hγex
