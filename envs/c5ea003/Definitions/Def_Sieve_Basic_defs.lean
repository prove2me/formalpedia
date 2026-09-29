-- Prove2me | Definitions.Def_Sieve_Basic_defs
-- name    : Sieve_Basic_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T03:54:54.93931+00:00
-- url     : https://prove2.me/theorems/394e717c-781a-41e0-a73e-aaa4584d3c51
-- title:
--   Sieve foundations: Selberg terms $g(d)$, upper/lower bound sieves ($\mu^{\pm}$), and the $\lambda^2$ construction
-- statement:
--   This bundle lays the foundations of the Selberg sieve on top of Mathlib's `BoundingSieve`/`SelbergSieve` framework. Throughout, a bounding sieve $s$ carries a density function $\nu$, a squarefree sifting modulus $P$ (product of the sifting primes), weights $a$, total mass $X$, and remainders $R_d$.
--
--   **Main definitions.**
--
--   - `selbergTerms s` — the arithmetic function $g(d) = \nu(d) \prod_{p \mid d} \frac{1}{1 - \nu(p)}$ (with the product over prime factors of $d$), the standard \"Selberg terms\" density companion to $\nu$; it is multiplicative and positive on divisors of $P$ (`selbergTerms_pos`, `selbergTerms_mult`).
--
--   - `UpperBoundSieve` / `LowerBoundSieve` — structures packaging a weight function $\mu^+ : \mathbb{N} \to \mathbb{R}$ (resp. $\mu^-$) together with the upper (resp. lower) Möbius property: $\sum_{d \mid n} \mu^+(d) \ge [n = 1]$ for all $n$ (`IsUpperMoebius`), resp. $\sum_{d \mid n} \mu^-(d) \le [n = 1]$ (`IsLowerMoebius`). These are the abstract majorants/minorants of the delta function used in every combinatorial sieve.
--
--   - `delta` — the indicator $\delta(n) = [n = 1]$ that sieve weights majorize or minorize.
--
--   - `lambdaSquared w` — the $\Lambda^2$ weight $d \mapsto \sum_{d_1, d_2 : \mathrm{lcm}(d_1,d_2) = d} w(d_1)\,w(d_2)$; the theorem `upperMoebius_of_lambda_sq` shows that whenever $w(1) = 1$, the divisor sum of $\lambda^2$ equals $\bigl(\sum_{d \mid n} w(d)\bigr)^2 \ge [n=1]$, so every normalized $\lambda^2$ weight is an upper bound sieve.
--
--   **Downstream use.** The Selberg sieve chooses the optimal weights $w = \gamma$ in the $\lambda^2$ construction, and $g$ appears in both the main term $X/S$ (through the bounding sum $S = \sum_{l^2 \le y,\ l \mid P} g(l)$) and the optimality analysis; the Brun–Titchmarsh application instantiates this machinery on intervals.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean (definitions vendored from this file)

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => SelbergSieve.selbergTerms s

theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def IsLowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

structure LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : IsLowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end UpperBoundSieve

section SieveLemmas


def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta


-- Unused ?

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult


end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0


theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s


end LambdaSquared

end SelbergSieve


