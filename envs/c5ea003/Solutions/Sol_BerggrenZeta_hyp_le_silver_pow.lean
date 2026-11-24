-- Prove2me | solution 1 for BerggrenZeta.hyp_le_silver_pow
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:19.712447+00:00
-- url     : https://prove2.me/submissions/c66bcbcd-bf0a-4f57-a907-a51d8dfd0cf7

-- Thm stub generated from Novelty/BerggrenTreeSilverGrowth.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# The silver growth dichotomy of the Berggren tree

The Berggren generators have spectral data governed by the units `3 ± 2√2 = (1 ± √2)²` of
`ℤ[√2]`.  This file makes the corresponding growth statements exact for the hypotenuse
`c(w) = m² + n²` of a node:

* `hyp_step_le_silver` — one Berggren move multiplies the hypotenuse by at most
  `3 + 2√2 = (1+√2)²`, the square of the silver ratio, for **all three** moves;
* `hyp_le_silver_pow` — hence `c(w) ≤ 5 · (3+2√2)^{|w|}`: the silver speed limit;
* `Mspine_hyp_lower`, `Mspine_silver_growth` — along the middle (Pell) spine the bound is
  attained up to a constant: `4 (3+2√2)^k ≤ c ≤ 5 (3+2√2)^k`;
* `Lspine_hyp`, `Rspine_hyp` — but along the two outer spines the hypotenuse grows only
  **quadratically**: `2k² + 6k + 5` and `4k² + 8k + 5`.

This dichotomy — exponential extremal branch, polynomial outer branches, `3^k` nodes at
depth `k` — is exactly what makes the abscissa of convergence of the tree zeta function
equal to `1` rather than the "silver" value `log 3 / (2 log(1+√2))` predicted by a purely
exponential branching model (see `Novelty.BerggrenTreeZetaAbscissa`).  The final result
`depth_slice_lower` quantifies the silver side: the depth-`k` slice of the tree zeta series
dominates the term `3^k (5 (3+2√2)^k)^{-s}` of the silver Ihara-type zeta of
`Novelty.BerggrenTreeCriticalLine`.
-/

open BerggrenZeta

-- open removed: section is not a namespace

/-! ## Part A. The silver speed limit -/

open Real
namespace BerggrenZeta

@[simp] theorem seed_nil : seed [] = (2, 1) := rfl

end BerggrenZeta

namespace BerggrenZeta

@[simp] theorem seedEquiv_apply (w : List (Fin 3)) : (seedEquiv w : ℕ × ℕ) = seed w := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem coprime_legs_of_seed {m n : ℕ} (h1 : n < m) (h3 : Nat.Coprime m n)
    (h4 : (m + n) % 2 = 1) : Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by
  obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  subst hk
  have hfac : (n + k) ^ 2 - n ^ 2 = k * (k + 2 * n) := by
    have : (n + k) ^ 2 = n ^ 2 + k * (k + 2 * n) := by ring
    omega
  have hodd : ((n + k) ^ 2 - n ^ 2) % 2 = 1 := by
    rw [hfac]
    have hk1 : Odd k := Nat.odd_iff.mpr (by omega)
    have hk2 : Odd (k + 2 * n) := Nat.odd_iff.mpr (by omega)
    exact Nat.odd_iff.mp (hk1.mul hk2)
  by_contra hcon
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  set m := n + k with hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpmn : p ∣ m ∨ p ∣ n := by
    have h2mn : p ∣ 2 * (m * n) := by rw [← mul_assoc]; exact hpb
    rcases (Nat.Prime.dvd_mul hp).mp h2mn with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by have := hp.two_le; omega)
    · exact (Nat.Prime.dvd_mul hp).mp h
  have hsqle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (le_of_lt h1) 2
  rcases hpmn with hmm | hn
  · have hm2 : p ∣ m ^ 2 := Dvd.dvd.pow hmm (by norm_num)
    have hn2 : p ∣ n ^ 2 := by
      have hsub := Nat.dvd_sub hm2 hpa
      rwa [show m ^ 2 - (m ^ 2 - n ^ 2) = n ^ 2 by omega] at hsub
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd hmm (hp.dvd_of_dvd_pow hn2)
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
  · have hn2 : p ∣ n ^ 2 := Dvd.dvd.pow hn (by norm_num)
    have hm2 : p ∣ m ^ 2 := by
      have := dvd_add hpa hn2
      rwa [show m ^ 2 - n ^ 2 + n ^ 2 = m ^ 2 by omega] at this
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd (hp.dvd_of_dvd_pow hm2) hn
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)

end BerggrenZeta

namespace BerggrenZeta

theorem node_isPPT (w : List (Fin 3)) :
    legOdd w ^ 2 + legEven w ^ 2 = hyp w ^ 2 ∧ 0 < legOdd w ∧ 0 < legEven w ∧
      Nat.Coprime (legOdd w) (legEven w) := by
  obtain ⟨h1, h2, h3, h4⟩ := seed_isSeed w
  have hsq : (seed w).2 ^ 2 < (seed w).1 ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [legOdd, legEven, hyp]
    zify [le_of_lt hsq]
    ring
  · simp only [legOdd]; omega
  · simp only [legEven]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) h2
  · simpa [legOdd, legEven] using BerggrenZeta.coprime_legs_of_seed h1 h3 h4

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_L (w : List (Fin 3)) :
    triple (0 :: w) =
      (let (a, b, c) := triple w; (a - 2 * b + 2 * c, 2 * a - b + 2 * c, 2 * a - 2 * b + 3 * c)) := by
  obtain ⟨h1, _, _, _⟩ := seed_isSeed w
  have h : ((2 * (seed w).1 - (seed w).2 : ℕ) : ℤ) = 2 * (seed w).1 - (seed w).2 := by
    have : (seed w).2 ≤ 2 * (seed w).1 := by omega
    push_cast [this]; ring
  simp only [triple, seed_cons, step, mvL, h]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_M (w : List (Fin 3)) :
    triple (1 :: w) =
      (let (a, b, c) := triple w; (a + 2 * b + 2 * c, 2 * a + b + 2 * c, 2 * a + 2 * b + 3 * c)) := by
  simp only [triple, seed_cons, step, mvM]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> push_cast <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem berggren_matrix_R (w : List (Fin 3)) :
    triple (2 :: w) =
      (let (a, b, c) := triple w;
        (-a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + 3 * c)) := by
  simp only [triple, seed_cons, step, mvR]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> push_cast <;> ring

end BerggrenZeta

namespace BerggrenZeta

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

end BerggrenZeta

namespace BerggrenZeta

theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  simp only [Real.sqrt_one] at h
  exact h

end BerggrenZeta

namespace BerggrenZeta

theorem silver_quad_M (m n : ℝ) :
    5 * m ^ 2 + 4 * m * n + n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2))
      = ((2 * Real.sqrt 2 - 2) * m - 2 * n) ^ 2 := by
    linear_combination (4 * n ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (5 * m ^ 2 + 4 * m * n + n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]

end BerggrenZeta

namespace BerggrenZeta

theorem silver_quad_R (m n : ℝ) :
    m ^ 2 + 4 * m * n + 5 * n ^ 2 ≤ (3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have hgt : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have key : (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2))
      = (2 * m - (2 * Real.sqrt 2 - 2) * n) ^ 2 := by
    linear_combination (4 * m ^ 2) * hs
  have hnn : 0 ≤ (2 * Real.sqrt 2 - 2) *
      ((3 + 2 * Real.sqrt 2) * (m ^ 2 + n ^ 2) - (m ^ 2 + 4 * m * n + 5 * n ^ 2)) := by
    rw [key]; positivity
  nlinarith [hnn, hgt]

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_step_le_silver (i : Fin 3) (w : List (Fin 3)) :
    (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := seed_isSeed w
  have h1' : ((seed w).2 : ℝ) < ((seed w).1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < ((seed w).2 : ℝ) := by exact_mod_cast h2
  have hs := BerggrenZeta.sqrt_two_sq
  have hsq := BerggrenZeta.one_le_sqrt_two
  set m : ℝ := ((seed w).1 : ℝ)
  set n : ℝ := ((seed w).2 : ℝ)
  fin_cases i
  · -- move `L`: `5m² - 4mn + n² ≤ 5 (m²+n²) ≤ (3+2√2)(m²+n²)`
    have hle : (seed w).2 ≤ 2 * (seed w).1 := by omega
    show ((hyp ((0 : Fin 3) :: w) : ℕ) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ)
    simp only [hyp, seed_cons, step, mvL]
    push_cast [hle]
    nlinarith
  · -- move `M`: the extremal (Pell) move
    simp only [hyp, seed_cons, step, mvM]
    push_cast
    have := BerggrenZeta.silver_quad_M m n
    nlinarith
  · -- move `R`
    simp only [hyp, seed_cons, step, mvR]
    push_cast
    have := BerggrenZeta.silver_quad_R m n
    nlinarith

end BerggrenZeta

namespace BerggrenZeta

@[simp] theorem hyp_nil : hyp [] = 5 := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem hyp_le_silver_pow (w : List (Fin 3)) :
    (hyp w : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hpos : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by positivity
    calc (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := BerggrenZeta.hyp_step_le_silver i w
      _ ≤ (3 + 2 * Real.sqrt 2) * (5 * (3 + 2 * Real.sqrt 2) ^ w.length) := by
          exact mul_le_mul_of_nonneg_left ih (le_of_lt hpos)
      _ = 5 * (3 + 2 * Real.sqrt 2) ^ (i :: w).length := by
          simp [List.length_cons, pow_succ]
          ring

end BerggrenZeta

namespace BerggrenZeta

theorem Lspine_seed (k : ℕ) : seed (Lspine k) = (k + 2, k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : Lspine (k + 1) = (0 : Fin 3) :: Lspine k := rfl
    rw [this, seed_cons, ih]
    simp only [step, mvL]
    exact Prod.ext (by simp; omega) (by simp)

end BerggrenZeta

namespace BerggrenZeta

theorem Rspine_seed (k : ℕ) : seed (Rspine k) = (2 * k + 2, 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : Rspine (k + 1) = (2 : Fin 3) :: Rspine k := rfl
    rw [this, seed_cons, ih]
    simp only [step, mvR]
    exact Prod.ext (by simp; omega) (by simp)

end BerggrenZeta

namespace BerggrenZeta

theorem Lspine_hyp (k : ℕ) : hyp (Lspine k) = 2 * k ^ 2 + 6 * k + 5 := by
  simp only [hyp, BerggrenZeta.Lspine_seed]
  ring

end BerggrenZeta

namespace BerggrenZeta

theorem Rspine_hyp (k : ℕ) : hyp (Rspine k) = 4 * k ^ 2 + 8 * k + 5 := by
  simp only [hyp, BerggrenZeta.Rspine_seed]
  ring

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_seed_succ (k : ℕ) :
    seed (Mspine (k + 1)) = (2 * (seed (Mspine k)).1 + (seed (Mspine k)).2,
      (seed (Mspine k)).1) := rfl

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_lower_invariant (k : ℕ) :
    2 * (1 + Real.sqrt 2) ^ k ≤ ((seed (Mspine k)).1 : ℝ) ∧
      2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) ≤ ((seed (Mspine k)).2 : ℝ) := by
  have hs := BerggrenZeta.sqrt_two_sq
  have h1 := BerggrenZeta.one_le_sqrt_two
  have hsle : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  induction k with
  | zero =>
    constructor
    · norm_num [Mspine, seed]
    · norm_num [Mspine, seed]
      linarith
  | succ k ih =>
    obtain ⟨ihm, ihn⟩ := ih
    have hpow : (0 : ℝ) < (1 + Real.sqrt 2) ^ k := by positivity
    rw [BerggrenZeta.Mspine_seed_succ]
    constructor
    · simp only
      push_cast
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) =
          2 * (2 * (1 + Real.sqrt 2) ^ k) + 2 * (1 + Real.sqrt 2) ^ k * (Real.sqrt 2 - 1) := by
        rw [pow_succ]
        ring
      rw [this]
      linarith
    · simp only
      have : 2 * (1 + Real.sqrt 2) ^ (k + 1) * (Real.sqrt 2 - 1) = 2 * (1 + Real.sqrt 2) ^ k := by
        rw [pow_succ]
        nlinarith
      rw [this]
      exact ihm

end BerggrenZeta

namespace BerggrenZeta

theorem Mspine_silver_growth (k : ℕ) :
    4 * (3 + 2 * Real.sqrt 2) ^ k ≤ (hyp (Mspine k) : ℝ) ∧
      (hyp (Mspine k) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
  have hs := BerggrenZeta.sqrt_two_sq
  have h1 := BerggrenZeta.one_le_sqrt_two
  constructor
  · obtain ⟨hm, -⟩ := BerggrenZeta.Mspine_lower_invariant k
    have hsq : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by nlinarith
    have hpow : ((1 + Real.sqrt 2) ^ k) ^ 2 = (3 + 2 * Real.sqrt 2) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, hsq]
    have hmpos : (0 : ℝ) ≤ 2 * (1 + Real.sqrt 2) ^ k := by positivity
    have hcast : (hyp (Mspine k) : ℝ)
        = ((seed (Mspine k)).1 : ℝ) ^ 2 + ((seed (Mspine k)).2 : ℝ) ^ 2 := by
      simp only [hyp]
      push_cast
      ring
    rw [hcast]
    nlinarith [sq_nonneg ((seed (Mspine k)).2 : ℝ)]
  · have := BerggrenZeta.hyp_le_silver_pow (Mspine k)
    simpa [Mspine, List.length_replicate] using this

end BerggrenZeta

namespace BerggrenZeta

theorem depth_slice_lower {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (3 : ℝ) ^ k * (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤
      ∑ v : Fin k → Fin 3, (hyp (List.ofFn v) : ℝ) ^ (-s) := by
  have hterm : ∀ v : Fin k → Fin 3,
      (5 * (3 + 2 * Real.sqrt 2) ^ k) ^ (-s) ≤ (hyp (List.ofFn v) : ℝ) ^ (-s) := by
    intro v
    have hlen : (List.ofFn v).length = k := by simp
    have hle : (hyp (List.ofFn v) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ k := by
      have := BerggrenZeta.hyp_le_silver_pow (List.ofFn v)
      rwa [hlen] at this
    have hpos : (0 : ℝ) < (hyp (List.ofFn v) : ℝ) := by
      have : 0 < hyp (List.ofFn v) := by
        obtain ⟨h1, h2, -, -⟩ := seed_isSeed (List.ofFn v)
        simp only [hyp]
        positivity
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hcard : (Finset.univ : Finset (Fin k → Fin 3)).card = 3 ^ k := by
    simp [Finset.card_univ]
  have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin k → Fin 3))
    (fun v => (hyp (List.ofFn v) : ℝ) ^ (-s)) _ (fun v _ => hterm v)
  rw [hcard, nsmul_eq_mul] at this
  simpa using this

end BerggrenZeta


theorem solution (w : List (Fin 3)) :
    (hyp w : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hpos : (0 : ℝ) < 3 + 2 * Real.sqrt 2 := by positivity
    calc (hyp (i :: w) : ℝ) ≤ (3 + 2 * Real.sqrt 2) * (hyp w : ℝ) := BerggrenZeta.hyp_step_le_silver i w
      _ ≤ (3 + 2 * Real.sqrt 2) * (5 * (3 + 2 * Real.sqrt 2) ^ w.length) := by
          exact mul_le_mul_of_nonneg_left ih (le_of_lt hpos)
      _ = 5 * (3 + 2 * Real.sqrt 2) ^ (i :: w).length := by
          simp [List.length_cons, pow_succ]
          ring

#print axioms solution
