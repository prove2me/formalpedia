-- Prove2me | solution 1 for BerggrenZeta.count_ge_silver_rpow
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:14.393406+00:00
-- url     : https://prove2.me/submissions/2041d390-c205-4223-af33-7515ec6ce767

-- Thm stub generated from Novelty/BerggrenTreeCounting.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCounting
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# Counting Berggren nodes below a height: the silver exponent as a lower bound

Let `N(H) = #{ w : c(w) ≤ H }` be the number of nodes of the Berggren tree whose hypotenuse
is at most `H`.  This file proves the two-sided estimate

* `nodesBelow_ncard_le` : `N(H) ≤ (⌊√H⌋ + 1)²`, so `N(H) = O(H)` — a consequence of the
  seed injectivity of `Novelty.BerggrenTreeZetaCore`, since a node with `c(w) = m²+n² ≤ H`
  has both Euclid parameters in `[0, √H]`;
* `silver_count_lower` / `count_ge_silver_rpow` : `N(H) ≥ 3^d` whenever `5(3+2√2)^d ≤ H`,
  hence `N(H) ≥ (1/3)·(H/5)^{σ₀}` with `σ₀ = log 3 / (2 log(1+√2))` the *silver abscissa*
  of `Novelty.BerggrenTreeCriticalLine`.

Together with `silverAbscissa_lt_one` this pins down the role of the silver exponent
exactly: the silver value `σ₀ ≈ 0.6237` is the growth exponent of the **depth-graded**
(purely exponential) model of the tree, and it is a genuine *lower* bound for the counting
function, but it is strictly smaller than the true abscissa of convergence `1` computed in
`Novelty.BerggrenTreeZetaAbscissa`.  The gap between `H^{σ₀}` and `H` is produced by the
polynomially growing outer spines (`Lspine_hyp`, `Rspine_hyp`), which contribute nodes far
below the silver speed limit.

## Lab notes (computed with `#eval` on the definitions of this development)

| `H`   | nodes with `c(w) ≤ H` | `(⌊√H⌋+1)²` | largest `d` with `5(3+2√2)^d ≤ H` | `3^d` |
|-------|----------------------|--------------|-----------------------------------|-------|
| 5     | 1                    | 9            | 0                                 | 1     |
| 50    | 7                    | 64           | 1                                 | 3     |
| 200   | 32                   | 225          | 2                                 | 9     |
| 1000  | 158                  | 1024         | 3                                 | 27    |

The counts (1, 7, 32, 158) — obtained by enumerating the admissible Euclid seeds `(m,n)`
with `m²+n² ≤ H`, which by `seedEquiv` is exactly the node count — confirm both bounds and
show that the truth sits strictly between `3^d ≍ H^{σ₀}` and `(√H+1)²`, in line with the
abscissa-`1` theorem (the counts grow essentially linearly in `H`).
-/

open BerggrenZeta

-- open removed: section is not a namespace







/-! ## Lower bound: the depth-`d` slice -/



/-! ## The silver exponent as a counting exponent -/

open Real
open Real Complex
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

namespace BerggrenZeta

theorem one_lt_silverUnit : (1 : ℝ) < silverUnit := by
  have := BerggrenZeta.one_le_sqrt_two
  simp only [silverUnit]
  linarith

end BerggrenZeta

namespace BerggrenZeta

theorem silverUnit_pos : (0 : ℝ) < silverUnit := by linarith [BerggrenZeta.one_lt_silverUnit]

end BerggrenZeta

namespace BerggrenZeta

theorem log_silverUnit_pos : 0 < Real.log silverUnit := Real.log_pos BerggrenZeta.one_lt_silverUnit

end BerggrenZeta

namespace BerggrenZeta

theorem silverUnit_sq : silverUnit ^ 2 = 3 + 2 * Real.sqrt 2 := by
  have := BerggrenZeta.sqrt_two_sq
  simp only [silverUnit]
  nlinarith

end BerggrenZeta

namespace BerggrenZeta

theorem norm_silver_ratio (s : ℂ) :
    ‖3 * (silverUnit : ℂ) ^ (-2 * s)‖ = 3 * Real.exp (Real.log silverUnit * (-2 * s.re)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos BerggrenZeta.silverUnit_pos,
    Real.rpow_def_of_pos BerggrenZeta.silverUnit_pos]
  norm_num

end BerggrenZeta

namespace BerggrenZeta

theorem norm_silver_ratio_lt_one_iff (s : ℂ) :
    ‖3 * (silverUnit : ℂ) ^ (-2 * s)‖ < 1 ↔ silverAbscissa < s.re := by
  rw [BerggrenZeta.norm_silver_ratio]
  have hL : 0 < Real.log silverUnit := BerggrenZeta.log_silverUnit_pos
  have hthree : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 3)]
    norm_num
  constructor
  · intro h
    have h1 : Real.exp (Real.log silverUnit * (-2 * s.re)) < Real.exp (-Real.log 3) := by
      rw [hthree]
      linarith
    have h2 := Real.exp_lt_exp.mp h1
    rw [silverAbscissa, div_lt_iff₀ (by positivity)]
    linarith
  · intro h
    rw [silverAbscissa, div_lt_iff₀ (by positivity)] at h
    have h2 : Real.log silverUnit * (-2 * s.re) < -Real.log 3 := by linarith
    have h3 := Real.exp_lt_exp.mpr h2
    rw [hthree] at h3
    linarith

end BerggrenZeta

namespace BerggrenZeta

theorem silverZeta_eq_tsum {s : ℂ} (hs : silverAbscissa < s.re) :
    ∑' k : ℕ, (3 : ℂ) ^ k * (silverUnit : ℂ) ^ (-2 * s * k) = silverZeta s := by
  have hnorm : ‖3 * (silverUnit : ℂ) ^ (-2 * s)‖ < 1 :=
    (BerggrenZeta.norm_silver_ratio_lt_one_iff s).mpr hs
  have hterm : ∀ k : ℕ, (3 : ℂ) ^ k * (silverUnit : ℂ) ^ (-2 * s * k)
      = (3 * (silverUnit : ℂ) ^ (-2 * s)) ^ k := by
    intro k
    rw [mul_pow, Complex.cpow_mul_nat]
  simp_rw [hterm]
  rw [tsum_geometric_of_norm_lt_one hnorm, silverZeta]

end BerggrenZeta

namespace BerggrenZeta

theorem silver_cpow_eq_exp (w : ℂ) :
    (silverUnit : ℂ) ^ w = Complex.exp (w * Real.log silverUnit) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast BerggrenZeta.silverUnit_pos.ne'),
    ← Complex.ofReal_log BerggrenZeta.silverUnit_pos.le, mul_comm]

end BerggrenZeta

namespace BerggrenZeta

theorem silver_denom_eq_zero_iff (s : ℂ) :
    1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0 ↔
      s.re = silverAbscissa ∧ ∃ k : ℤ, s.im = k * Real.pi / Real.log silverUnit := by
  have hL : 0 < Real.log silverUnit := BerggrenZeta.log_silverUnit_pos
  have hLC : (Real.log silverUnit : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h3 : Complex.exp (-(Real.log 3 : ℂ)) = 1 / 3 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ) < 3)]
    norm_num
  have hiff : (1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0) ↔
      Complex.exp (-2 * s * (Real.log silverUnit : ℂ))
        = Complex.exp (-(Real.log 3 : ℂ)) := by
    rw [BerggrenZeta.silver_cpow_eq_exp, h3]
    constructor
    · intro h
      linear_combination (-1 / 3 : ℂ) * h
    · intro h
      linear_combination (-3 : ℂ) * h
  rw [hiff, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    have hs_eq : s = ((Real.log 3 / (2 * Real.log silverUnit) : ℝ) : ℂ)
        + ((-(n : ℝ) * Real.pi / Real.log silverUnit : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination -hn
    refine ⟨?_, ⟨-n, ?_⟩⟩
    · rw [hs_eq, silverAbscissa]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · rw [hs_eq]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      push_cast
      ring
  · rintro ⟨hre, k, him⟩
    refine ⟨-k, ?_⟩
    have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    rw [hs, hre, him, silverAbscissa]
    push_cast
    field_simp
    ring

end BerggrenZeta

namespace BerggrenZeta

theorem silver_pole_re_eq {s : ℂ} (h : 1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0) :
    s.re = silverAbscissa := ((BerggrenZeta.silver_denom_eq_zero_iff s).mp h).1

end BerggrenZeta

namespace BerggrenZeta

theorem silver_pole_shift {s : ℂ} (h : 1 - 3 * (silverUnit : ℂ) ^ (-2 * s) = 0) :
    1 - 3 * (silverUnit : ℂ) ^
      (-2 * (s + Complex.I * ((Real.pi / Real.log silverUnit : ℝ) : ℂ))) = 0 := by
  obtain ⟨hre, k, him⟩ := (BerggrenZeta.silver_denom_eq_zero_iff s).mp h
  have hL : 0 < Real.log silverUnit := BerggrenZeta.log_silverUnit_pos
  refine (BerggrenZeta.silver_denom_eq_zero_iff _).mpr ⟨?_, ⟨k + 1, ?_⟩⟩
  · simpa using hre
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_add, mul_zero]
    rw [him]
    push_cast
    field_simp

end BerggrenZeta

namespace BerggrenZeta

theorem silver_denom_analytic (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => 1 - 3 * (silverUnit : ℂ) ^ (-2 * z)) s := by
  have h2 : (fun z : ℂ => 1 - 3 * (silverUnit : ℂ) ^ (-2 * z))
      = fun z : ℂ => 1 - 3 * Complex.exp ((-2 * z) * (Real.log silverUnit : ℂ)) := by
    funext z
    rw [BerggrenZeta.silver_cpow_eq_exp]
  rw [h2]
  apply Differentiable.analyticAt
  fun_prop

end BerggrenZeta

namespace BerggrenZeta

theorem silverZeta_analyticAt {s : ℂ} (hs : 1 - 3 * (silverUnit : ℂ) ^ (-2 * s) ≠ 0) :
    AnalyticAt ℂ silverZeta s :=
  (BerggrenZeta.silver_denom_analytic s).inv hs

end BerggrenZeta

namespace BerggrenZeta

theorem silverZeta_meromorphicOn : MeromorphicOn silverZeta Set.univ := by
  intro s _
  exact ((BerggrenZeta.silver_denom_analytic s).meromorphicAt).inv

end BerggrenZeta

namespace BerggrenZeta

theorem silverAbscissa_lt_one : silverAbscissa < 1 := by
  have hL : 0 < Real.log silverUnit := BerggrenZeta.log_silverUnit_pos
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := BerggrenZeta.sqrt_two_sq
    nlinarith [Real.sqrt_nonneg 2]
  have hlt : Real.log 3 < 2 * Real.log silverUnit := by
    have hpow : Real.log (silverUnit ^ 2) = 2 * Real.log silverUnit := by
      rw [Real.log_pow]
      norm_num
    rw [← hpow, BerggrenZeta.silverUnit_sq]
    exact Real.log_lt_log (by norm_num) (by linarith)
  rw [silverAbscissa, div_lt_one (by positivity)]
  exact hlt

end BerggrenZeta

namespace BerggrenZeta

theorem silverAbscissa_pos : 0 < silverAbscissa := by
  have hL : 0 < Real.log silverUnit := BerggrenZeta.log_silverUnit_pos
  rw [silverAbscissa]
  apply div_pos (Real.log_pos (by norm_num))
  positivity

end BerggrenZeta

namespace BerggrenZeta

theorem seed_le_sqrt {H : ℕ} {w : List (Fin 3)} (hw : w ∈ nodesBelow H) :
    (seed w).1 ≤ Nat.sqrt H ∧ (seed w).2 ≤ Nat.sqrt H := by
  have h : (seed w).1 ^ 2 + (seed w).2 ^ 2 ≤ H := hw
  constructor
  · exact Nat.le_sqrt'.2 (le_trans (Nat.le_add_right _ _) h)
  · exact Nat.le_sqrt'.2 (le_trans (Nat.le_add_left _ _) h)

end BerggrenZeta

namespace BerggrenZeta

private def seedBox (H : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (Nat.sqrt H + 1) ×ˢ Finset.range (Nat.sqrt H + 1)

end BerggrenZeta

namespace BerggrenZeta

private theorem seed_image_subset (H : ℕ) :
    seed '' nodesBelow H ⊆ (BerggrenZeta.seedBox H : Set (ℕ × ℕ)) := by
  rintro p ⟨w, hw, rfl⟩
  obtain ⟨h1, h2⟩ := BerggrenZeta.seed_le_sqrt hw
  simp only [BerggrenZeta.seedBox, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le h1, Nat.lt_succ_of_le h2⟩

end BerggrenZeta

namespace BerggrenZeta

theorem nodesBelow_finite (H : ℕ) : (nodesBelow H).Finite := by
  refine Set.Finite.of_finite_image ?_ (seed_injective.injOn)
  exact Set.Finite.subset (BerggrenZeta.seedBox H).finite_toSet (BerggrenZeta.seed_image_subset H)

end BerggrenZeta

namespace BerggrenZeta

theorem nodesBelow_ncard_le (H : ℕ) :
    (nodesBelow H).ncard ≤ (Nat.sqrt H + 1) ^ 2 := by
  have h1 : (seed '' nodesBelow H).ncard = (nodesBelow H).ncard :=
    Set.ncard_image_of_injective _ seed_injective
  have h2 : (seed '' nodesBelow H).ncard ≤ ((BerggrenZeta.seedBox H : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).ncard :=
    Set.ncard_le_ncard (BerggrenZeta.seed_image_subset H) (BerggrenZeta.seedBox H).finite_toSet
  rw [h1] at h2
  refine h2.trans ?_
  rw [Set.ncard_coe_finset]
  simp [BerggrenZeta.seedBox, Finset.card_product, pow_two]

end BerggrenZeta

namespace BerggrenZeta

theorem ofFn_mem_nodesBelow {d H : ℕ} (h : 5 * (3 + 2 * Real.sqrt 2) ^ d ≤ (H : ℝ))
    (f : Fin d → Fin 3) : List.ofFn f ∈ nodesBelow H := by
  have hlen : (List.ofFn f).length = d := List.length_ofFn
  have hle : (hyp (List.ofFn f) : ℝ) ≤ 5 * (3 + 2 * Real.sqrt 2) ^ d := by
    have := BerggrenZeta.hyp_le_silver_pow (List.ofFn f)
    rwa [hlen] at this
  have : (hyp (List.ofFn f) : ℝ) ≤ (H : ℝ) := hle.trans h
  exact_mod_cast this

end BerggrenZeta

namespace BerggrenZeta

theorem silver_count_lower {d H : ℕ} (h : 5 * (3 + 2 * Real.sqrt 2) ^ d ≤ (H : ℝ)) :
    3 ^ d ≤ (nodesBelow H).ncard := by
  have hsub : (fun f : Fin d → Fin 3 => List.ofFn f) '' Set.univ ⊆ nodesBelow H := by
    rintro w ⟨f, -, rfl⟩
    exact BerggrenZeta.ofFn_mem_nodesBelow h f
  have hcard : ((fun f : Fin d → Fin 3 => List.ofFn f) '' Set.univ).ncard = 3 ^ d := by
    rw [Set.ncard_image_of_injective _ List.ofFn_injective, Set.ncard_univ]
    simp
  calc 3 ^ d = ((fun f : Fin d → Fin 3 => List.ofFn f) '' Set.univ).ncard := hcard.symm
    _ ≤ (nodesBelow H).ncard := Set.ncard_le_ncard hsub (BerggrenZeta.nodesBelow_finite H)

end BerggrenZeta

namespace BerggrenZeta

private theorem silver_sq_gt_one : (1 : ℝ) < 3 + 2 * Real.sqrt 2 := by
  have := Real.sqrt_nonneg 2
  linarith

end BerggrenZeta

namespace BerggrenZeta

private theorem log_silver_sq :
    Real.log (3 + 2 * Real.sqrt 2) = 2 * Real.log silverUnit := by
  have h : (3 : ℝ) + 2 * Real.sqrt 2 = silverUnit ^ 2 := (BerggrenZeta.silverUnit_sq).symm
  rw [h, Real.log_pow]
  push_cast
  ring

end BerggrenZeta

namespace BerggrenZeta

theorem count_ge_silver_rpow {H : ℕ} (hH : 5 ≤ H) :
    (1 / 3 : ℝ) * ((H : ℝ) / 5) ^ silverAbscissa ≤ ((nodesBelow H).ncard : ℝ) := by
  set A : ℝ := 3 + 2 * Real.sqrt 2 with hA
  have hA1 : (1 : ℝ) < A := BerggrenZeta.silver_sq_gt_one
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hH5 : (1 : ℝ) ≤ (H : ℝ) / 5 := by
    have : (5 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  have hHpos : (0 : ℝ) < (H : ℝ) / 5 := by linarith
  have hlogH : 0 ≤ Real.log ((H : ℝ) / 5) := Real.log_nonneg hH5
  set L : ℝ := Real.log ((H : ℝ) / 5) / Real.log A with hL
  have hL0 : 0 ≤ L := div_nonneg hlogH hlogA.le
  set d : ℕ := ⌊L⌋₊ with hd
  have hdL : (d : ℝ) ≤ L := Nat.floor_le hL0
  have hLd : L < (d : ℝ) + 1 := Nat.lt_floor_add_one L
  -- the depth-`d` slice fits below `H`
  have hfit : 5 * A ^ d ≤ (H : ℝ) := by
    have h1 : (A : ℝ) ^ (d : ℝ) ≤ A ^ L := by
      exact (Real.rpow_le_rpow_left_iff hA1).2 hdL
    have h2 : (A : ℝ) ^ L = (H : ℝ) / 5 := by
      have hmul : Real.log A * L = Real.log ((H : ℝ) / 5) := by
        rw [hL]
        field_simp
      rw [Real.rpow_def_of_pos hApos, hmul, Real.exp_log hHpos]
    have h3 : (A : ℝ) ^ d ≤ (H : ℝ) / 5 := by
      rw [← Real.rpow_natCast A d]
      rw [h2] at h1
      exact h1
    linarith
  have hcount : (3 : ℝ) ^ d ≤ ((nodesBelow H).ncard : ℝ) := by
    have := BerggrenZeta.silver_count_lower (d := d) (H := H) hfit
    exact_mod_cast this
  refine le_trans ?_ hcount
  -- `(1/3)(H/5)^{σ₀} ≤ 3^d`
  have hsig : silverAbscissa = Real.log 3 / Real.log A := by
    rw [silverAbscissa, BerggrenZeta.log_silver_sq]
  have hkey : ((H : ℝ) / 5) ^ silverAbscissa = (3 : ℝ) ^ L := by
    rw [hsig, Real.rpow_def_of_pos hHpos, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), hL]
    congr 1
    field_simp
  rw [hkey]
  have h1 : (3 : ℝ) ^ L ≤ 3 ^ ((d : ℝ) + 1) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 3)).2 hLd.le
  have h2 : (3 : ℝ) ^ ((d : ℝ) + 1) = 3 * 3 ^ d := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    ring
  rw [h2] at h1
  linarith

end BerggrenZeta


theorem solution {H : ℕ} (hH : 5 ≤ H) :
    (1 / 3 : ℝ) * ((H : ℝ) / 5) ^ silverAbscissa ≤ ((nodesBelow H).ncard : ℝ) := by
  set A : ℝ := 3 + 2 * Real.sqrt 2 with hA
  have hA1 : (1 : ℝ) < A := BerggrenZeta.silver_sq_gt_one
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  have hH5 : (1 : ℝ) ≤ (H : ℝ) / 5 := by
    have : (5 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    linarith
  have hHpos : (0 : ℝ) < (H : ℝ) / 5 := by linarith
  have hlogH : 0 ≤ Real.log ((H : ℝ) / 5) := Real.log_nonneg hH5
  set L : ℝ := Real.log ((H : ℝ) / 5) / Real.log A with hL
  have hL0 : 0 ≤ L := div_nonneg hlogH hlogA.le
  set d : ℕ := ⌊L⌋₊ with hd
  have hdL : (d : ℝ) ≤ L := Nat.floor_le hL0
  have hLd : L < (d : ℝ) + 1 := Nat.lt_floor_add_one L
  -- the depth-`d` slice fits below `H`
  have hfit : 5 * A ^ d ≤ (H : ℝ) := by
    have h1 : (A : ℝ) ^ (d : ℝ) ≤ A ^ L := by
      exact (Real.rpow_le_rpow_left_iff hA1).2 hdL
    have h2 : (A : ℝ) ^ L = (H : ℝ) / 5 := by
      have hmul : Real.log A * L = Real.log ((H : ℝ) / 5) := by
        rw [hL]
        field_simp
      rw [Real.rpow_def_of_pos hApos, hmul, Real.exp_log hHpos]
    have h3 : (A : ℝ) ^ d ≤ (H : ℝ) / 5 := by
      rw [← Real.rpow_natCast A d]
      rw [h2] at h1
      exact h1
    linarith
  have hcount : (3 : ℝ) ^ d ≤ ((nodesBelow H).ncard : ℝ) := by
    have := BerggrenZeta.silver_count_lower (d := d) (H := H) hfit
    exact_mod_cast this
  refine le_trans ?_ hcount
  -- `(1/3)(H/5)^{σ₀} ≤ 3^d`
  have hsig : silverAbscissa = Real.log 3 / Real.log A := by
    rw [silverAbscissa, BerggrenZeta.log_silver_sq]
  have hkey : ((H : ℝ) / 5) ^ silverAbscissa = (3 : ℝ) ^ L := by
    rw [hsig, Real.rpow_def_of_pos hHpos, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), hL]
    congr 1
    field_simp
  rw [hkey]
  have h1 : (3 : ℝ) ^ L ≤ 3 ^ ((d : ℝ) + 1) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 3)).2 hLd.le
  have h2 : (3 : ℝ) ^ ((d : ℝ) + 1) = 3 * 3 ^ d := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    ring
  rw [h2] at h1
  linarith

#print axioms solution
