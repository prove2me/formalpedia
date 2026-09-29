-- Prove2me | solution 1 for LinearOptimization.integer_polyhedron_points_natGenerated
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T03:23:11.985932+00:00
-- url     : https://prove2.me/submissions/306f2181-86bb-40a0-ade0-711f6870ed87

import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Tactic
import Definitions.Def_LinearOptimization_LagrangeanDual

open Matrix
open LinearOptimization

private abbrev HullIndex (m n : ℕ) :=
  Fin n ⊕ Fin n ⊕ Fin m ⊕ Unit

private abbrev HullCode (m n : ℕ) := HullIndex m n → ℕ

private def posCoord {m n : ℕ} (z : HullCode m n) (j : Fin n) : ℕ := z (.inl j)
private def negCoord {m n : ℕ} (z : HullCode m n) (j : Fin n) : ℕ := z (.inr (.inl j))
private def slackCoord {m n : ℕ} (z : HullCode m n) (i : Fin m) : ℕ :=
  z (.inr (.inr (.inl i)))
private def timeCoord {m n : ℕ} (z : HullCode m n) : ℕ :=
  z (.inr (.inr (.inr ())))

private def decodeZ {m n : ℕ} : HullCode m n →+ (Fin n → ℤ) where
  toFun z j := (posCoord z j : ℤ) - (negCoord z j : ℤ)
  map_zero' := by ext; simp [posCoord, negCoord]
  map_add' z z' := by
    ext j
    change (((posCoord z j + posCoord z' j : ℕ) : ℤ) -
        ((negCoord z j + negCoord z' j : ℕ) : ℤ)) =
      ((posCoord z j : ℤ) - (negCoord z j : ℤ)) +
        ((posCoord z' j : ℤ) - (negCoord z' j : ℤ))
    push_cast
    ring

private def decodeR {m n : ℕ} : HullCode m n →+ (Fin n → ℝ) where
  toFun z j := (decodeZ z j : ℝ)
  map_zero' := by ext; simp [decodeZ]
  map_add' z z' := by
    ext j
    change ((decodeZ (z + z') j : ℤ) : ℝ) =
      (decodeZ z j : ℤ) + (decodeZ z' j : ℤ)
    rw [map_add]
    simp

private def grade {m n : ℕ} : HullCode m n →+ ℕ where
  toFun z := timeCoord z
  map_zero' := rfl
  map_add' _ _ := rfl

private def constraintLHS {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ) :
    HullCode m n →+ (Fin m → ℤ) where
  toFun z i := ∑ j, D i j * decodeZ z j
  map_zero' := by ext; simp [decodeZ]
  map_add' z z' := by
    ext i
    change (∑ j, D i j * decodeZ (z + z') j) =
      (∑ j, D i j * decodeZ z j) + ∑ j, D i j * decodeZ z' j
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private def constraintRHS {m n : ℕ} (d : Fin m → ℤ) :
    HullCode m n →+ (Fin m → ℤ) where
  toFun z i := (grade z : ℤ) * d i + (slackCoord z i : ℤ)
  map_zero' := by ext; simp [grade]
  map_add' z z' := by
    ext i
    simp [grade, timeCoord, slackCoord]
    ring

private def solutionMonoid {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ)
    (d : Fin m → ℤ) : AddSubmonoid (HullCode m n) :=
  (constraintLHS D).eqLocusM (constraintRHS d)

private lemma int_split (z : ℤ) :
    (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by
  omega

private lemma feasible_iff_code {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ)
    (y : Fin n → ℝ) :
    y ∈ lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i ↦ (d i : ℝ)) ↔
      ∃ z : HullCode m n,
        z ∈ solutionMonoid D d ∧ grade z = 1 ∧ y = decodeR z := by
  classical
  constructor
  · rintro ⟨hyD, hyZ⟩
    choose u hu using hyZ
    let val : Fin m → ℤ := fun i ↦ ∑ j, D i j * u j
    have hval : ∀ i, d i ≤ val i := by
      intro i
      have hi := hyD i
      change (d i : ℝ) ≤ ∑ j, (D i j : ℝ) * y j at hi
      have hyu : ∀ j, y j = (u j : ℝ) := hu
      simp_rw [hyu] at hi
      exact_mod_cast hi
    let z : HullCode m n := fun e ↦
      match e with
      | .inl j => (u j).toNat
      | .inr (.inl j) => (-u j).toNat
      | .inr (.inr (.inl i)) => (val i - d i).toNat
      | .inr (.inr (.inr _)) => 1
    refine ⟨z, ?_, rfl, ?_⟩
    · change constraintLHS D z = constraintRHS d z
      funext i
      have hnonneg : 0 ≤ val i - d i := sub_nonneg.mpr (hval i)
      dsimp [constraintLHS, constraintRHS, grade, decodeZ, posCoord, negCoord,
        slackCoord, timeCoord, z]
      simp_rw [int_split]
      rw [Int.toNat_of_nonneg hnonneg]
      simp [val]
    · ext j
      dsimp [decodeR, decodeZ, posCoord, negCoord, z]
      rw [hu j]
      exact_mod_cast (int_split (u j)).symm
  · rintro ⟨z, hz, hgrade, rfl⟩
    constructor
    · intro i
      have hi := congrFun hz i
      change (∑ j, D i j * decodeZ z j) =
        (grade z : ℤ) * d i + (slackCoord z i : ℤ) at hi
      change (d i : ℝ) ≤
        ∑ j, (D i j : ℝ) * (decodeZ z j : ℝ)
      rw [hgrade] at hi
      have hslack : (0 : ℤ) ≤ (slackCoord z i : ℤ) := by positivity
      have hzineq : d i ≤ ∑ j, D i j * decodeZ z j := by omega
      exact_mod_cast hzineq
    · intro j
      exact ⟨decodeZ z j, rfl⟩

/-- Bertsimas--Tsitsiklis, Exercise 11.8(c), p. 525, in a form that also
handles empty integer sets and lineality by homogenized Gordan generation. -/
theorem solution {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ) :
    ∃ (k r : ℕ) (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)),
      lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i ↦ (d i : ℝ)) =
        {y | ∃ (i : Fin k) (q : Fin r → ℕ),
          y = x i + ∑ j, (q j : ℝ) • w j} := by
  classical
  let H : AddSubmonoid (HullCode m n) := solutionMonoid D d
  have hfg : H.FG := AddSubmonoid.fg_eqLocusM (constraintLHS D) (constraintRHS d)
  obtain ⟨S, hS⟩ := hfg
  let B : Finset (HullCode m n) := S.filter (fun z ↦ grade z = 1)
  let eS : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let baseCode : Fin (Fintype.card B) → HullCode m n := fun i ↦ (eB.symm i).1
  let rayCode : Fin (Fintype.card S) → HullCode m n := fun j ↦
    let z := (eS.symm j).1
    if grade z = 0 then z else 0
  let x : Fin (Fintype.card B) → (Fin n → ℝ) := fun i ↦ decodeR (baseCode i)
  let w : Fin (Fintype.card S) → (Fin n → ℝ) := fun j ↦ decodeR (rayCode j)
  refine ⟨Fintype.card B, Fintype.card S, x, w, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨z, hzH, hzgrade, hyz⟩ := (feasible_iff_code D d y).mp hy
    have hzclosure : z ∈ AddSubmonoid.closure (S : Set (HullCode m n)) := by
      rw [hS]
      exact hzH
    obtain ⟨a, ha⟩ := (AddSubmonoid.mem_closure_finset').mp hzclosure
    have htime : ∑ s : S, a s * grade (s : HullCode m n) = 1 := by
      have ht := congrArg grade ha
      rw [hzgrade] at ht
      symm at ht
      simpa [grade, timeCoord] using ht
    have hnonzero : (∑ s : S, a s * grade (s : HullCode m n)) ≠ 0 := by
      rw [htime]
      decide
    obtain ⟨s0, hs0mem, hs0ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hnonzero
    have hs0le : a s0 * grade (s0 : HullCode m n) ≤ 1 := by
      rw [← htime]
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun s : S ↦ a s * grade (s : HullCode m n))
        (fun _ _ ↦ Nat.zero_le _) hs0mem
    have hs0prod : a s0 * grade (s0 : HullCode m n) = 1 := by omega
    have ha0 : a s0 = 1 :=
      Nat.eq_one_of_dvd_one ⟨grade (s0 : HullCode m n), hs0prod.symm⟩
    have hg0 : grade (s0 : HullCode m n) = 1 :=
      Nat.eq_one_of_dvd_one ⟨a s0, by simpa [Nat.mul_comm] using hs0prod.symm⟩
    let b0 : B := ⟨s0.1, by simp [B, s0.2, hg0]⟩
    let i0 : Fin (Fintype.card B) := eB b0
    have hbase : baseCode i0 = (s0 : HullCode m n) := by
      simp [baseCode, i0, b0]
    have hrest : ∀ s : S, s ≠ s0 →
        a s * grade (s : HullCode m n) = 0 := by
      let f : S → ℕ := fun s ↦ a s * grade (s : HullCode m n)
      have herase : ∑ s ∈ (Finset.univ.erase s0), f s = 0 := by
        have hdecomp := Finset.sum_erase_add Finset.univ f (Finset.mem_univ s0)
        change (∑ s ∈ (Finset.univ.erase s0), f s) + f s0 =
          ∑ s ∈ Finset.univ, f s at hdecomp
        have hf0 : f s0 = 1 := hs0prod
        have hfall : ∑ s ∈ Finset.univ, f s = 1 := htime
        omega
      intro s hne
      have hsmem : s ∈ Finset.univ.erase s0 := by simp [hne]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ.erase s0)
        (f := f) (fun _ _ ↦ Nat.zero_le _)).mp herase s hsmem
      exact hz
    let qS : S → ℕ := fun s ↦ if s = s0 then 0 else a s
    let q : Fin (Fintype.card S) → ℕ := fun j ↦ qS (eS.symm j)
    refine ⟨i0, q, ?_⟩
    have hterm : ∀ s : S,
        q (eS s) • rayCode (eS s) = qS s • (s : HullCode m n) := by
      intro s
      by_cases hs : s = s0
      · subst s
        simp [q, qS]
      · by_cases haz : a s = 0
        · simp [q, qS, rayCode, hs, haz]
        · have hprod := hrest s hs
          have hgs : grade (s : HullCode m n) = 0 := by
            rcases Nat.mul_eq_zero.mp hprod with ha' | hg'
            · exact (haz ha').elim
            · exact hg'
          simp [q, qS, rayCode, hs, hgs]
    have hreindex :
        (∑ j, q j • rayCode j) = ∑ s : S, qS s • (s : HullCode m n) := by
      calc
        (∑ j, q j • rayCode j) = ∑ s : S, q (eS s) • rayCode (eS s) := by
          exact (Fintype.sum_equiv eS
            (fun s : S ↦ q (eS s) • rayCode (eS s))
            (fun j ↦ q j • rayCode j) (fun _ ↦ rfl)).symm
        _ = ∑ s : S, qS s • (s : HullCode m n) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hterm s
    have hqerase : (∑ s : S, qS s • (s : HullCode m n)) =
        ∑ s ∈ (Finset.univ.erase s0), a s • (s : HullCode m n) := by
      have hz0 : qS s0 • (s0 : HullCode m n) = 0 := by simp [qS]
      have herase := Finset.sum_erase (s := Finset.univ)
        (f := fun s : S ↦ qS s • (s : HullCode m n)) hz0
      rw [← herase]
      apply Finset.sum_congr rfl
      intro s hs
      have hne : s ≠ s0 := by simpa using hs
      simp [qS, hne]
    have hdecomp := Finset.sum_erase_add Finset.univ
      (fun s : S ↦ a s • (s : HullCode m n)) (Finset.mem_univ s0)
    have hcode : z = baseCode i0 + ∑ j, q j • rayCode j := by
      rw [hbase, hreindex, hqerase]
      calc
        z = ∑ s : S, a s • (s : HullCode m n) := ha
        _ = (∑ s ∈ (Finset.univ.erase s0), a s • (s : HullCode m n)) +
            a s0 • (s0 : HullCode m n) := hdecomp.symm
        _ = (s0 : HullCode m n) +
            ∑ s ∈ (Finset.univ.erase s0), a s • (s : HullCode m n) := by
              rw [ha0, one_nsmul]
              abel
    calc
      y = decodeR z := hyz
      _ = decodeR (baseCode i0 + ∑ j, q j • rayCode j) := by rw [hcode]
      _ = x i0 + ∑ j, (q j : ℝ) • w j := by
        ext c
        simp [x, w, decodeR, decodeZ, posCoord, negCoord]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        ring
  · rintro ⟨i, q, rfl⟩
    have hbaseB : baseCode i ∈ B := by
      exact (eB.symm i).2
    have hbasePair : baseCode i ∈ S ∧ grade (baseCode i) = 1 := by
      simpa [B] using hbaseB
    have hbaseS : baseCode i ∈ S := by
      exact hbasePair.1
    have hbaseGrade : grade (baseCode i) = 1 := by
      exact hbasePair.2
    have hbaseH : baseCode i ∈ H := by
      rw [← hS]
      exact AddSubmonoid.subset_closure hbaseS
    have hrayH : ∀ j, rayCode j ∈ H := by
      intro j
      let s : S := eS.symm j
      by_cases hs : grade (s : HullCode m n) = 0
      · have hsH : (s : HullCode m n) ∈ H := by
          rw [← hS]
          exact AddSubmonoid.subset_closure s.2
        simpa [rayCode, s, hs] using hsH
      · simp [rayCode, s, hs]
    have hrayGrade : ∀ j, grade (rayCode j) = 0 := by
      intro j
      let s : S := eS.symm j
      by_cases hs : grade (s : HullCode m n) = 0
      · simpa [rayCode, s, hs]
      · simp [rayCode, s, hs]
    let z : HullCode m n := baseCode i + ∑ j, q j • rayCode j
    have hzH : z ∈ H := by
      apply H.add_mem hbaseH
      exact H.sum_mem fun j _ ↦ H.nsmul_mem (hrayH j) (q j)
    have hzgrade : grade z = 1 := by
      rw [show grade z = grade (baseCode i) +
          grade (∑ j, q j • rayCode j) by simp [z]]
      rw [hbaseGrade]
      have hzero : grade (∑ j, q j • rayCode j) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [map_nsmul, hrayGrade j, nsmul_zero]
      rw [hzero, add_zero]
    apply (feasible_iff_code D d _).mpr
    refine ⟨z, ?_, hzgrade, ?_⟩
    · simpa [H] using hzH
    · ext c
      simp [z, x, w, decodeR, decodeZ, posCoord, negCoord]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
