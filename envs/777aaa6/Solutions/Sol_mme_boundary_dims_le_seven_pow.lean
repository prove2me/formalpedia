-- Prove2me | solution 1 for mme_boundary_dims_le_seven_pow
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-19T19:39:18.434551+00:00
-- url     : https://prove2.me/submissions/83cec400-c356-4fa2-b516-d8f271e454ad

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators
open MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit

set_option autoImplicit false

theorem solution : forall (ell N : Nat) (P : MME.ProfiledCW.Predicate N)
    (B : MME.ProfiledCW.BoundaryEnd ell N P), B.a * B.b * B.c <= 7 ^ N := by
  intro ell N P B
  classical
  have hword : forall (K : Nat),
      (∑ s : (Fin K → Fin 3), (5:ℕ) ^ ((Finset.univ.filter (fun r => s r = 1)).card))
        = 7 ^ K := by
    intro K
    induction K with
    | zero => decide
    | succ K ih =>
      let e : (Fin (K+1) → Fin 3) ≃ ((Fin K → Fin 3) × Fin 3) :=
        { toFun := fun s => (Fin.tail s, s 0),
          invFun := fun p => Fin.cons p.2 p.1,
          left_inv := fun s => Fin.cons_self_tail s,
          right_inv := fun p => by simp only [Fin.tail_cons, Fin.cons_zero] }
      have step1 : (∑ s : (Fin (K+1) → Fin 3),
            (5:ℕ) ^ ((Finset.univ.filter (fun r => s r = 1)).card))
          = ∑ p : ((Fin K → Fin 3) × Fin 3),
            (5:ℕ) ^ ((Finset.univ.filter
              (fun r => (Fin.cons p.2 p.1 : Fin (K+1) → Fin 3) r = 1)).card) :=
        Fintype.sum_equiv e
          (fun s : Fin (K+1) → Fin 3 => (5:ℕ) ^ ((Finset.univ.filter (fun r => s r = 1)).card))
          (fun p : (Fin K → Fin 3) × Fin 3 => (5:ℕ) ^ ((Finset.univ.filter
            (fun r => (Fin.cons p.2 p.1 : Fin (K+1) → Fin 3) r = 1)).card))
          (fun s => congrArg (fun w : Fin (K+1) → Fin 3 =>
            (5:ℕ) ^ ((Finset.univ.filter (fun r => w r = 1)).card))
            (Fin.cons_self_tail s).symm)
      have hsplit : ∀ (t : Fin K → Fin 3) (v : Fin 3),
          (Finset.univ.filter (fun r : Fin (K+1) => (Fin.cons v t : Fin (K+1) → Fin 3) r = 1)).card
          = (Finset.univ.filter (fun r : Fin K => t r = 1)).card + (if v = 1 then 1 else 0) := by
        intro t v
        rw [Finset.card_filter, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← Finset.card_filter]
        exact add_comm _ _
      have hexp : ∀ (t : Fin K → Fin 3) (v : Fin 3),
          (5:ℕ) ^ ((Finset.univ.filter (fun r : Fin (K+1) => (Fin.cons v t : Fin (K+1) → Fin 3) r = 1)).card)
          = (5:ℕ) ^ ((Finset.univ.filter (fun r : Fin K => t r = 1)).card)
            * (if v = 1 then 5 else 1) := by
        intro t v
        rw [hsplit t v, pow_add]
        congr 1
        by_cases h : v = 1 <;> simp [h]
      have h7 : (∑ v : Fin 3, (if v = 1 then (5:ℕ) else 1)) = 7 := by
        rw [Fin.sum_univ_three]
        decide
      rw [step1, Fintype.sum_prod_type]
      simp only [hexp, ← Finset.sum_mul, h7, ← Finset.mul_sum, ih, ← pow_succ]
  have hwordC : (∑ s : CompleteWord ell, (5:ℕ) ^ Boundary.ones s) = 7 ^ (2 ^ (ell - 1)) := by
    unfold Boundary.ones
    exact hword _
  have hpart : ∀ j : Fin B.partition.parts,
      (B.profile j).dim
        ≤ (∑ s : CompleteWord ell, (5:ℕ) ^ Boundary.ones s) ^ (B.partition.size j) := by
    intro j
    have e1 : (Nat.factorial (B.partition.size j) / ∏ s, (((B.profile j).count s).factorial))
        = Nat.multinomial Finset.univ ((B.profile j).count) := by
      unfold Nat.multinomial
      rw [(B.profile j).total]
    have e2 : (5:ℕ) ^ (∑ s, (B.profile j).count s * Boundary.ones s)
        = ∏ s, ((5:ℕ) ^ Boundary.ones s) ^ ((B.profile j).count s) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro s _
      rw [mul_comm ((B.profile j).count s) (Boundary.ones s), pow_mul]
    have edim : (B.profile j).dim
        = Nat.multinomial Finset.univ ((B.profile j).count)
          * ∏ s ∈ Finset.univ, ((5:ℕ) ^ Boundary.ones s) ^ ((B.profile j).count s) := by
      unfold Boundary.Profile.dim
      rw [e1, e2]
    rw [edim, Finset.sum_pow_eq_sum_piAntidiag]
    simp only [Nat.cast_id]
    have hmem : (B.profile j).count ∈ Finset.piAntidiag Finset.univ (B.partition.size j) :=
      Finset.mem_piAntidiag.mpr ⟨(B.profile j).total, fun i _ => Finset.mem_univ i⟩
    exact Finset.single_le_sum
      (f := fun k => Nat.multinomial Finset.univ k * ∏ s, ((5:ℕ) ^ Boundary.ones s) ^ (k s))
      (fun k _ => Nat.zero_le _) hmem
  have hprod : B.a * B.b * B.c = ∏ j, (B.profile j).dim := by
    unfold BoundaryEnd.a BoundaryEnd.b BoundaryEnd.c
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    unfold Boundary.Profile.a Boundary.Profile.b Boundary.Profile.c
    have htri : ∀ z : Fin 3,
        (if z = 1 then (B.profile j).dim else 1)
        * (if z = 2 then (B.profile j).dim else 1)
        * (if z = 0 then (B.profile j).dim else 1) = (B.profile j).dim := by
      intro z
      fin_cases z <;> simp
    exact htri _
  have hcard2 : ∑ j, B.partition.size j = B.L := by
    have he := Fintype.card_congr B.partition.positions
    rw [Fintype.card_sigma] at he
    simpa using he
  have hKN : 2 ^ (ell - 1) * B.L = N := by
    rw [mul_comm]
    exact B.length
  have hpart7 : ∀ j : Fin B.partition.parts,
      (B.profile j).dim ≤ 7 ^ (2 ^ (ell - 1) * B.partition.size j) := by
    intro j
    have h1 := hpart j
    rw [hwordC] at h1
    rwa [← pow_mul] at h1
  rw [hprod]
  calc ∏ j, (B.profile j).dim
      ≤ ∏ j, 7 ^ (2 ^ (ell - 1) * B.partition.size j) :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hpart7 i)
    _ = 7 ^ N := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, hcard2, hKN]
