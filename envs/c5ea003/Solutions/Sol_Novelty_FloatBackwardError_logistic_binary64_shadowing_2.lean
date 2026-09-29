-- Prove2me | solution 2 for Novelty.FloatBackwardError.logistic_binary64_shadowing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T18:03:01.952972+00:00
-- url     : https://prove2.me/submissions/88ce8f80-c4f1-458b-8985-d802b150f34b

import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

open Novelty.FloatBackwardError in
theorem solution (M : RoundingModel) (hu : M.u ≤ (2:ℝ) ^ (-53 : ℤ))
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (N : ℕ)
    (hstay : ∀ n ≤ N, flOrbit M logisticCoeffs x₀ n ∈ Set.Icc (0:ℝ) 1) :
    ∀ n ≤ N, |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n|
      ≤ (2:ℝ) ^ (-46 : ℤ) * (((4:ℝ) ^ n - 1) / 3) := by
  classical
  have hu0 : 0 ≤ M.u := M.u_nonneg
  have hu53 : (2:ℝ) ^ (-53 : ℤ) ≤ 1 / 100 := by norm_num
  have h46 : (2:ℝ) ^ (-46 : ℤ) = 128 * (2:ℝ) ^ (-53 : ℤ) := by norm_num
  have hu1 : M.u ≤ 1 / 100 := hu.trans hu53
  -- one relative error step
  have hstep : ∀ a e s : ℝ, |a - 1| ≤ s → |e| ≤ M.u → |a * (1 + e) - 1| ≤ s + M.u + s * M.u := by
    intro a e s ha he
    have hs : 0 ≤ s := (abs_nonneg _).trans ha
    have eq : a * (1 + e) - 1 = (a - 1) + e + (a - 1) * e := by ring
    rw [eq]
    calc |(a - 1) + e + (a - 1) * e| ≤ |a - 1| + |e| + |(a - 1) * e| := abs_add_three _ _ _
      _ = |a - 1| + |e| + |a - 1| * |e| := by rw [abs_mul]
      _ ≤ s + M.u + s * M.u :=
          add_le_add (add_le_add ha he) (mul_le_mul ha he (abs_nonneg _) hs)
  -- the rounding defect of one Horner step of the logistic map
  have hdef : ∀ y ∈ Set.Icc (0:ℝ) 1,
      |hornerFl M logisticCoeffs y - logistic y| ≤ (2:ℝ) ^ (-46 : ℤ) := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have m0 : M.mul y 0 = 0 := by
      obtain ⟨e, -, h⟩ := M.mul_spec y 0
      rw [h]
      ring
    obtain ⟨e1, he1, h1⟩ := M.add_spec (-4) (M.mul y 0)
    obtain ⟨e2, he2, h2⟩ := M.mul_spec y (M.add (-4) (M.mul y 0))
    obtain ⟨e3, he3, h3⟩ := M.add_spec 4 (M.mul y (M.add (-4) (M.mul y 0)))
    obtain ⟨e4, he4, h4⟩ := M.mul_spec y (M.add 4 (M.mul y (M.add (-4) (M.mul y 0))))
    obtain ⟨e5, he5, h5⟩ := M.add_spec 0 (M.mul y (M.add 4 (M.mul y (M.add (-4) (M.mul y 0)))))
    simp only [logisticCoeffs, hornerFl]
    rw [h5, h4, h3, h2, h1, m0]
    have hA0 : |(1 + e1) - 1| ≤ M.u := by simpa using he1
    have hA := hstep (1 + e1) e2 M.u hA0 he2
    have hB0 : |(1 + e3) - 1| ≤ M.u := by simpa using he3
    have hB1 := hstep (1 + e3) e4 M.u hB0 he4
    have hB := hstep ((1 + e3) * (1 + e4)) e5 _ hB1 he5
    obtain ⟨A, hAdef⟩ : ∃ A, A = (1 + e1) * (1 + e2) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = (1 + e3) * (1 + e4) * (1 + e5) := ⟨_, rfl⟩
    rw [← hAdef] at hA
    rw [← hBdef] at hB
    have hA' : |A - 1| ≤ 3 * M.u := by nlinarith
    have hB' : |B - 1| ≤ 4 * M.u := by nlinarith
    have hBabs : |B| ≤ 1 + 4 * M.u := by
      have := abs_sub_abs_le_abs_sub B 1
      rw [abs_one] at this
      linarith
    have heq : (0 + y * ((4 + y * ((-4 + 0) * (1 + e1)) * (1 + e2)) * (1 + e3)) * (1 + e4))
          * (1 + e5) - logistic y = 4 * y * ((1 - y) * (B - 1) - y * (A - 1) * B) := by
      rw [hAdef, hBdef]
      simp only [logistic]
      ring
    rw [heq, abs_mul, abs_mul]
    have hy4 : |(4:ℝ)| * |y| ≤ 4 := by
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4), abs_of_nonneg hy0]
      linarith
    have hin : |(1 - y) * (B - 1) - y * (A - 1) * B| ≤ 4 * M.u + 3 * M.u * (1 + 4 * M.u) := by
      calc |(1 - y) * (B - 1) - y * (A - 1) * B|
          ≤ |(1 - y) * (B - 1)| + |y * (A - 1) * B| := abs_sub _ _
        _ = |1 - y| * |B - 1| + |y| * |A - 1| * |B| := by rw [abs_mul, abs_mul, abs_mul]
        _ ≤ 1 * (4 * M.u) + 1 * (3 * M.u) * (1 + 4 * M.u) := by
          have e1' : |1 - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          have e2' : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          gcongr
        _ = 4 * M.u + 3 * M.u * (1 + 4 * M.u) := by ring
    have hin' : 0 ≤ |(1 - y) * (B - 1) - y * (A - 1) * B| := abs_nonneg _
    calc |(4:ℝ)| * |y| * |(1 - y) * (B - 1) - y * (A - 1) * B|
        ≤ 4 * (4 * M.u + 3 * M.u * (1 + 4 * M.u)) :=
          mul_le_mul hy4 hin hin' (by norm_num)
      _ = 28 * M.u + 48 * (M.u * M.u) := by ring
      _ ≤ 128 * (2:ℝ) ^ (-53 : ℤ) := by
          have hq : M.u * M.u ≤ M.u * (1 / 100) := mul_le_mul_of_nonneg_left hu1 hu0
          linarith
      _ = (2:ℝ) ^ (-46 : ℤ) := h46.symm
  -- the exact orbit stays in [0,1]
  have hlog01 : ∀ x ∈ Set.Icc (0:ℝ) 1, logistic x ∈ Set.Icc (0:ℝ) 1 := by
    intro x hx
    obtain ⟨h0, h1⟩ := hx
    simp only [logistic, Set.mem_Icc]
    constructor <;> nlinarith [sq_nonneg (2 * x - 1)]
  have htrue : ∀ n, trueOrbit logistic x₀ n ∈ Set.Icc (0:ℝ) 1 := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => exact hlog01 _ ih
  -- local Lipschitz bound for the logistic map
  have hlip : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      |logistic y - logistic x| ≤ 4 * max y (1 - y) * |y - x| := by
    intro x y hx hy
    have e : logistic y - logistic x = 4 * (y - x) * (1 - x - y) := by
      simp only [logistic]
      ring
    have h1 : |1 - x - y| ≤ max y (1 - y) := by
      rw [abs_le]
      constructor
      · have := le_max_left y (1 - y)
        linarith [hx.2]
      · have := le_max_right y (1 - y)
        linarith [hx.1]
    rw [e, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    calc 4 * |y - x| * |1 - x - y| ≤ 4 * |y - x| * max y (1 - y) := by gcongr
      _ = 4 * max y (1 - y) * |y - x| := by ring
  intro n hn
  induction n with
  | zero => simp [flOrbit, trueOrbit]
  | succ n ih =>
    have hy := hstay n (by omega)
    have hx := htrue n
    have ihn := ih (by omega)
    have hmax : max (flOrbit M logisticCoeffs x₀ n) (1 - flOrbit M logisticCoeffs x₀ n) ≤ 1 :=
      max_le hy.2 (by linarith [hy.1])
    have hmax0 : 0 ≤ max (flOrbit M logisticCoeffs x₀ n) (1 - flOrbit M logisticCoeffs x₀ n) :=
      le_max_of_le_left hy.1
    show |hornerFl M logisticCoeffs (flOrbit M logisticCoeffs x₀ n)
        - logistic (trueOrbit logistic x₀ n)| ≤ (2:ℝ) ^ (-46 : ℤ) * (((4:ℝ) ^ (n + 1) - 1) / 3)
    calc |hornerFl M logisticCoeffs (flOrbit M logisticCoeffs x₀ n)
          - logistic (trueOrbit logistic x₀ n)|
        ≤ |hornerFl M logisticCoeffs (flOrbit M logisticCoeffs x₀ n)
              - logistic (flOrbit M logisticCoeffs x₀ n)|
          + |logistic (flOrbit M logisticCoeffs x₀ n) - logistic (trueOrbit logistic x₀ n)| :=
          abs_sub_le _ _ _
      _ ≤ (2:ℝ) ^ (-46 : ℤ) + 4 * max (flOrbit M logisticCoeffs x₀ n)
            (1 - flOrbit M logisticCoeffs x₀ n)
            * |flOrbit M logisticCoeffs x₀ n - trueOrbit logistic x₀ n| :=
          add_le_add (hdef _ hy) (hlip _ _ hx hy)
      _ ≤ (2:ℝ) ^ (-46 : ℤ) + 4 * 1 * ((2:ℝ) ^ (-46 : ℤ) * (((4:ℝ) ^ n - 1) / 3)) := by
          gcongr
      _ = (2:ℝ) ^ (-46 : ℤ) * (((4:ℝ) ^ (n + 1) - 1) / 3) := by ring
