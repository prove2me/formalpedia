-- Prove2me | solution 1 for trace_pow_eq_walk
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T21:13:51.918088+00:00
-- url     : https://prove2.me/submissions/a971b1eb-5963-41ee-a7de-274366a6834e

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

open Matrix
open scoped BigOperators

namespace TracePowWalkSol

def finCycleSucc {m : Nat} [NeZero m] (k : Fin m) : Fin m :=
  ⟨(k.1 + 1) % m, Nat.mod_lt _ (Nat.pos_of_neZero m)⟩

def pathVertices {ι : Type*} {n : Nat} (a : ι) (p : Fin n → ι) (b : ι) :
    Fin (n + 2) → ι :=
  Fin.snoc (Fin.cons a p) b

def pathWeight {ι R : Type*} [CommMonoid R] {n : Nat} (M : Matrix ι ι R)
    (a : ι) (p : Fin n → ι) (b : ι) : R :=
  ∏ k : Fin (n + 1), M (pathVertices a p b k.castSucc) (pathVertices a p b k.succ)

def cyclicWeight {ι R : Type*} [CommMonoid R] {n : Nat} (M : Matrix ι ι R)
    (v : Fin (n + 1) → ι) : R :=
  ∏ k : Fin (n + 1), M (v k) (v (finCycleSucc k))

lemma snoc_zero_succ_eq_cycle {ι : Type*} {n : Nat} (v : Fin (n + 1) → ι)
    (k : Fin (n + 1)) :
    (Fin.snoc (α := fun _ => ι) v (v 0)) k.succ = v (finCycleSucc k) := by
  by_cases hk : k.1 + 1 < n + 1
  · have hcycle : finCycleSucc k = (⟨k.1 + 1, hk⟩ : Fin (n + 1)) := by
      ext
      simp [finCycleSucc, Nat.mod_eq_of_lt hk]
    have hsucc : k.succ = (⟨k.1 + 1, hk⟩ : Fin (n + 1)).castSucc := by
      ext
      rfl
    rw [hcycle, hsucc, Fin.snoc_castSucc]
  · have hkval : k.1 + 1 = n + 1 := by omega
    have hsucc : k.succ = Fin.last (n + 1) := by
      ext
      simp [hkval]
    have hcycle : finCycleSucc k = 0 := by
      ext
      simp [finCycleSucc, hkval]
    rw [hcycle, hsucc, Fin.snoc_last]

lemma pathWeight_closed_eq_cyclic {ι R : Type*} [CommRing R] {n : Nat}
    (M : Matrix ι ι R) (a : ι) (p : Fin n → ι) :
    pathWeight M a p a = cyclicWeight M (Fin.cons a p) := by
  apply Finset.prod_congr rfl
  intro k hk
  simp only [pathVertices, Fin.snoc_castSucc]
  let v : Fin (n + 1) → ι := Fin.cons (α := fun _ => ι) a p
  change
    M (v k) ((Fin.snoc (α := fun _ => ι) v a) k.succ) =
      M (v k) (v (finCycleSucc k))
  simpa [v] using congrArg (fun x => M (v k) x)
    (snoc_zero_succ_eq_cycle v k)

lemma pathWeight_snoc {ι R : Type*} [CommRing R] {n : Nat} (M : Matrix ι ι R)
    (a : ι) (p : Fin n → ι) (c b : ι) :
    pathWeight M a (Fin.snoc p c) b = pathWeight M a p c * M c b := by
  rw [pathWeight, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [pathVertices, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc]
    rw [Fin.succ_castSucc k]
    simp only [Fin.snoc_castSucc]
  · simp [pathVertices, Fin.cons_snoc_eq_snoc_cons]

lemma pow_succ_apply_eq_path_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (M : Matrix ι ι R) :
    ∀ (n : Nat) (a b : ι),
      (M ^ (n + 1)) a b = ∑ p : Fin n → ι, pathWeight M a p b
  | 0, a, b => by
      simp [pathWeight, pathVertices]
      rw [show (1 : Fin 2) = Fin.last 1 by rfl, Fin.snoc_last]
  | n + 1, a, b => by
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [pow_succ_apply_eq_path_sum M n]
      calc
        (∑ x : ι, (∑ p : Fin n → ι, pathWeight M a p x) * M x b)
            = ∑ x : ι, ∑ p : Fin n → ι, pathWeight M a p x * M x b := by
                simp [Finset.sum_mul]
        _ = ∑ xp : ι × (Fin n → ι), pathWeight M a xp.2 xp.1 * M xp.1 b := by
                rw [Fintype.sum_prod_type]
        _ = ∑ q : Fin (n + 1) → ι, pathWeight M a q b := by
                exact Fintype.sum_equiv
                  (Fin.snocEquiv (fun _ : Fin (n + 1) => ι))
                  (fun xp : ι × (Fin n → ι) => pathWeight M a xp.2 xp.1 * M xp.1 b)
                  (fun q : Fin (n + 1) → ι => pathWeight M a q b)
                  (by
                    intro xp
                    exact (pathWeight_snoc M a xp.2 xp.1 b).symm)

end TracePowWalkSol

open TracePowWalkSol

theorem solution {iota : Type*} [Fintype iota] [DecidableEq iota]
    {R : Type*} [CommRing R] (M : Matrix iota iota R) (n : Nat) :
    Matrix.trace (M ^ (n + 1)) =
      ∑ v : Fin (n + 1) → iota,
        ∏ k : Fin (n + 1),
          M (v k) (v ⟨(k.1 + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩) := by
  classical
  have hkey : Matrix.trace (M ^ (n + 1)) =
      Finset.univ.sum (fun v : Fin (n + 1) → iota =>
        Finset.univ.prod (fun k : Fin (n + 1) => M (v k) (v (finCycleSucc k)))) := by
    rw [Matrix.trace]
    simp_rw [Matrix.diag_apply]
    simp_rw [pow_succ_apply_eq_path_sum M n]
    calc
      (∑ x : iota, ∑ p : Fin n → iota, pathWeight M x p x)
          = ∑ xp : iota × (Fin n → iota), pathWeight M xp.1 xp.2 xp.1 := by
              exact (Fintype.sum_prod_type
                (fun xp : iota × (Fin n → iota) => pathWeight M xp.1 xp.2 xp.1)).symm
      _ = ∑ v : Fin (n + 1) → iota, cyclicWeight M v := by
              exact Fintype.sum_equiv
                (Fin.consEquiv (fun _ : Fin (n + 1) => iota))
                (fun xp : iota × (Fin n → iota) => pathWeight M xp.1 xp.2 xp.1)
                (fun v : Fin (n + 1) → iota => cyclicWeight M v)
                (by
                  intro xp
                  exact pathWeight_closed_eq_cyclic M xp.1 xp.2)
      _ = Finset.univ.sum (fun v : Fin (n + 1) → iota =>
            Finset.univ.prod (fun k : Fin (n + 1) => M (v k) (v (finCycleSucc k)))) := rfl
  rw [hkey]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro k _
  have : (⟨(k.1 + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      = finCycleSucc k := by
    ext; simp [finCycleSucc]
  rw [this]
