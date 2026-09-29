-- Prove2me | solution 1 for PriceOfUniversality.price_unbounded_in_parameters
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:31.614914+00:00
-- url     : https://prove2.me/submissions/2cf42a45-c91b-4991-984e-26d7fc907b8e

-- Sol generated from Novelty/UniversalRedundancyPi.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyPi
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_bernClass_isPMF
import Theorems.Thm_PriceOfUniversality_code_regret_ge_logb_shtarkov
import Theorems.Thm_PriceOfUniversality_exists_eq_maxLik
import Theorems.Thm_PriceOfUniversality_le_maxLik
import Theorems.Thm_PriceOfUniversality_logb_shtarkov_bernClass_ge
import Theorems.Thm_PriceOfUniversality_shtarkov_pos
/-
# The price of universality, VII: the full `k`-parameter Rissanen rate

`UniversalRedundancyProduct.lean` proved that the Shtarkov sum is multiplicative
over a product of *two* independent classes.  Here we upgrade this to an
arbitrary finite family of independent components,

  `S(⨂ i, P i) = ∏ i, S(P i)`,  hence  `regret(⨂ i, P i) = ∑ i, regret(P i)`,

and combine it with the `√n` lower bound for the memoryless binary class to
obtain the genuine **`k`-parameter Rissanen rate**: every code for `k`
independent binary blocks of length `n` must pay, on some message and against
some member of the class,

  `k · ((1/2) log₂ n − 2)`  bits of regret,

while the normalised maximum likelihood code pays at most
`k · log₂ (n + 1)` bits.  So the price of universality for a `k`-parameter
memoryless model is `Θ(k log n)`: *linear in the number of free parameters,
logarithmic in the block length.*

The research verdict this file supports: a decompressor specialised to one
component of the model class buys back exactly the regret of that component and
nothing more, and those savings add up over independent components.
-/

open PriceOfUniversality

open Finset Real


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)]
variable {Θ : ι → Type*} [∀ i, Fintype (Θ i)] [∀ i, Nonempty (Θ i)]


/-- Summing a product over all tuples factorises into a product of sums. -/
theorem sum_pi_prod (f : ∀ i, A i → ℝ) :
    ∑ x : (∀ i, A i), ∏ i, f i (x i) = ∏ i, ∑ a : A i, f i a := by
  rw [Finset.prod_univ_sum (fun i => (univ : Finset (A i))) f, Fintype.piFinset_univ]

omit [∀ i, Fintype (Θ i)] [∀ i, Nonempty (Θ i)] in
/-- A product of PMFs over independent components is a PMF on tuples. -/
theorem piClass_isPMF {p : ∀ i, Θ i → A i → ℝ} (hp : ∀ i θ, IsPMF (p i θ))
    (t : ∀ i, Θ i) : IsPMF (piClass p t) := by
  refine ⟨fun x => Finset.prod_nonneg fun i _ => (hp i (t i)).nonneg (x i), ?_⟩
  simp only [piClass]
  rw [sum_pi_prod fun i a => p i (t i) a]
  exact Finset.prod_eq_one fun i _ => (hp i (t i)).total

/-- **The maximum likelihood factorises over independent components.** -/
theorem maxLik_piClass {p : ∀ i, Θ i → A i → ℝ} (hp : ∀ i θ, IsPMF (p i θ))
    (x : ∀ i, A i) : maxLik (piClass p) x = ∏ i, maxLik (p i) (x i) := by
  refine le_antisymm ?_ ?_
  · refine (Finset.sup'_le_iff univ_nonempty _).2 fun t _ => ?_
    exact Finset.prod_le_prod (fun i _ => (hp i (t i)).nonneg (x i))
      (fun i _ => le_maxLik (p i) (t i) (x i))
  · choose t ht using fun i => exists_eq_maxLik (p i) (x i)
    calc ∏ i, maxLik (p i) (x i) = piClass p t x :=
          Finset.prod_congr rfl fun i _ => ht i
      _ ≤ maxLik (piClass p) x := le_maxLik (piClass p) t x

/-- **Multiplicativity of the Shtarkov sum over a finite family of independent
components.** -/
theorem shtarkov_piClass {p : ∀ i, Θ i → A i → ℝ} (hp : ∀ i θ, IsPMF (p i θ)) :
    shtarkov (piClass p) = ∏ i, shtarkov (p i) := by
  calc shtarkov (piClass p) = ∑ x : (∀ i, A i), ∏ i, maxLik (p i) (x i) :=
        Finset.sum_congr rfl fun x _ => maxLik_piClass hp x
    _ = ∏ i, ∑ a : A i, maxLik (p i) a := sum_pi_prod fun i a => maxLik (p i) a
    _ = ∏ i, shtarkov (p i) := rfl

/-- **Additivity of the price of universality**: the exact minimax regret of a
product class is the sum of the minimax regrets of the components. -/
theorem logb_shtarkov_piClass {p : ∀ i, Θ i → A i → ℝ} (hp : ∀ i θ, IsPMF (p i θ)) :
    logb 2 (shtarkov (piClass p)) = ∑ i, logb 2 (shtarkov (p i)) := by
  rw [shtarkov_piClass hp]
  exact Real.logb_prod _ _ fun i _ => ne_of_gt (shtarkov_pos (hp i))


/-! ## The `k`-parameter Rissanen rate for memoryless binary blocks -/


theorem kBernClass_isPMF (k n : ℕ) (t : Fin k → Fin (n + 1)) : IsPMF (kBernClass k n t) :=
  piClass_isPMF (fun _ => bernClass_isPMF n) t

/-- **The `k`-parameter Rissanen lower bound on the Shtarkov sum.** -/
theorem logb_shtarkov_kBernClass_ge (k n : ℕ) (hn : 1 ≤ n) :
    (k : ℝ) * ((1/2) * Real.logb 2 n - 2) ≤ Real.logb 2 (shtarkov (kBernClass k n)) := by
  rw [kBernClass, logb_shtarkov_piClass (fun _ => bernClass_isPMF n)]
  calc (k : ℝ) * ((1/2) * Real.logb 2 n - 2)
      = ∑ _i : Fin k, ((1/2) * Real.logb 2 n - 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ ∑ _i : Fin k, Real.logb 2 (shtarkov (bernClass n)) :=
        Finset.sum_le_sum fun i _ => logb_shtarkov_bernClass_ge n hn


/-- **Rissanen's `(k/2) log n` rate, formalised with explicit constants.**
Every prefix-free code for `k` independent binary blocks of length `n` pays, on
some message and against some member of the class, a regret of at least
`k · ((1/2) log₂ n − 2)` bits over the ideal codelength of the best member. -/
theorem kBlock_bernoulli_regret_ge (k n : ℕ) (hn : 1 ≤ n)
    {L : (Fin k → Msg n) → ℕ} (hL : IsCode L) :
    ∃ (j : Fin k → Fin (n + 1)) (x : Fin k → Msg n),
      (k : ℝ) * ((1/2) * Real.logb 2 n - 2) ≤ (L x : ℝ) + Real.logb 2 (kBernClass k n j x) := by
  obtain ⟨j, x, hjx⟩ :=
    code_regret_ge_logb_shtarkov (p := kBernClass k n) (L := L) (kBernClass_isPMF k n) hL
  exact ⟨j, x, le_trans (logb_shtarkov_kBernClass_ge k n hn) hjx⟩




open PriceOfUniversality in
theorem solution(C : ℝ) (n : ℕ) (hn : 32 ≤ n) :
    ∃ k : ℕ, ∀ {L : (Fin k → Msg n) → ℕ}, IsCode L →
      ∃ (j : Fin k → Fin (n + 1)) (x : Fin k → Msg n),
        C ≤ (L x : ℝ) + Real.logb 2 (kBernClass k n j x) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hgap : (0:ℝ) < (1/2) * Real.logb 2 n - 2 := by
    have hn32 : (32:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hlog : Real.logb 2 32 ≤ Real.logb 2 (n:ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn32
    have h32v : Real.logb 2 (32:ℝ) = 5 := by
      rw [show (32:ℝ) = 2 ^ (5:ℕ) by norm_num, Real.logb_pow]
      simp [Real.logb_self_eq_one]
    rw [h32v] at hlog
    linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ((1/2) * Real.logb 2 n - 2))
  refine ⟨k, fun {L} hL => ?_⟩
  obtain ⟨j, x, hjx⟩ := kBlock_bernoulli_regret_ge k n hn1 hL
  refine ⟨j, x, le_trans ?_ hjx⟩
  rw [div_lt_iff₀ hgap] at hk
  linarith
