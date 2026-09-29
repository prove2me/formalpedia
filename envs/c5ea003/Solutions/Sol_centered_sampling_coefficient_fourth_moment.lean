-- Prove2me | solution 1 for centered_sampling_coefficient_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T22:57:28.43237+00:00
-- url     : https://prove2.me/submissions/fa2182d2-024b-4f47-8df7-429f880f761f

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_quadruple
import Theorems.Thm_bernoulli_powerset_expectation_prod_factor
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 3200000
set_option maxRecDepth 8000

/-- `Coeff` rewritten as a coordinate sum of centered terms `h_w(𝟙[w∈Ω])`. -/
private theorem coeff_eq_linear {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Omega p B) =
      ∑ w : Fin n₁ × Fin n₂, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)) := by
  classical
  unfold matrixEntrySum centeredSamplingFluctuation samplingProjection
  apply Finset.sum_congr rfl
  intro w _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases h : (w.1, w.2) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-- **General four-coordinate factorization.** For any four coordinates and any
four single-coordinate functions, the expectation of the product factorizes (by
independence) into the product over ALL coordinates of the Bernoulli-weighted
local product `p·F u 1 + (1-p)·F u 0`, where `F u` is the product of those `g`'s
whose coordinate equals `u`. Uniform over all equality patterns of `a,b,c,d`. -/
private theorem four_coord_factor {n₁ n₂ : ℕ} (p : ℝ)
    (a b c d : Fin n₁ × Fin n₂) (ga gb gc gd : ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ga (if a ∈ Omega then 1 else 0) * gb (if b ∈ Omega then 1 else 0)
          * gc (if c ∈ Omega then 1 else 0) * gd (if d ∈ Omega then 1 else 0)) =
      ∏ u : Fin n₁ × Fin n₂,
        (p * ((if a = u then ga 1 else 1) * (if b = u then gb 1 else 1)
              * (if c = u then gc 1 else 1) * (if d = u then gd 1 else 1))
         + (1 - p) * ((if a = u then ga 0 else 1) * (if b = u then gb 0 else 1)
              * (if c = u then gc 0 else 1) * (if d = u then gd 0 else 1))) := by
  classical
  set F : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun u x => (if a = u then ga x else 1) * (if b = u then gb x else 1)
      * (if c = u then gc x else 1) * (if d = u then gd x else 1) with hF
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p F
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ u : Fin n₁ × Fin n₂, F u (if u ∈ Omega then 1 else 0)) =
      (fun Omega => ga (if a ∈ Omega then 1 else 0) * gb (if b ∈ Omega then 1 else 0)
          * gc (if c ∈ Omega then 1 else 0) * gd (if d ∈ Omega then 1 else 0)) := by
    funext Omega
    -- split the product over univ into the four relevant factors
    have ha : a ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)) := Finset.mem_univ a
    -- compute each F u (𝟙_u): only matters at u = a,b,c,d
    rw [show (∏ u : Fin n₁ × Fin n₂, F u (if u ∈ Omega then 1 else 0))
          = ∏ u : Fin n₁ × Fin n₂,
              ((if a = u then ga (if a ∈ Omega then 1 else 0) else 1)
               * (if b = u then gb (if b ∈ Omega then 1 else 0) else 1)
               * (if c = u then gc (if c ∈ Omega then 1 else 0) else 1)
               * (if d = u then gd (if d ∈ Omega then 1 else 0) else 1)) from ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [Finset.prod_ite_eq, Finset.prod_ite_eq, Finset.prod_ite_eq, Finset.prod_ite_eq]
      simp only [Finset.mem_univ, if_true]
    · apply Finset.prod_congr rfl; intro u _
      simp only [hF]
      by_cases hau : a = u <;> by_cases hbu : b = u <;> by_cases hcu : c = u <;>
        by_cases hdu : d = u <;>
        simp only [hau, hbu, hcu, hdu, if_true, if_false]
  rw [hL] at key
  rw [key]

/-- The single-coordinate `k`-th raw moment of the centered term `h_w`. -/
private def rawMom (p : ℝ) (hw1 hw0 : ℝ) (k : ℕ) : ℝ := p * hw1 ^ k + (1 - p) * hw0 ^ k

/-- **Abstract four-coordinate evaluation under mean-zero.** For four single-
coordinate functions `ga,gb,gc,gd`, each with zero Bernoulli mean
(`p·g 1 + (1-p)·g 0 = 0`), the four-fold expectation collapses (independence +
mean-zero) to the partition value: all-equal → 4th raw moment, two distinct pairs
→ product of the two 2nd raw moments, anything with a multiplicity-1 index → 0.
Stated with opaque `g`'s so the 64-way equality case split operates on small
polynomial goals (avoiding `whnf` blow-up from the concrete centered terms). -/
private theorem four_coord_eval {n₁ n₂ : ℕ} (p : ℝ)
    (a b c d : Fin n₁ × Fin n₂) (ga gb gc gd : ℝ → ℝ)
    (hma : p * ga 1 + (1 - p) * ga 0 = 0) (hmb : p * gb 1 + (1 - p) * gb 0 = 0)
    (hmc : p * gc 1 + (1 - p) * gc 0 = 0) (hmd : p * gd 1 + (1 - p) * gd 0 = 0) :
    bernoulliExpectation p
        (fun Omega => ga (if a ∈ Omega then 1 else 0) * gb (if b ∈ Omega then 1 else 0)
          * gc (if c ∈ Omega then 1 else 0) * gd (if d ∈ Omega then 1 else 0)) =
      (if a = b then (if c = d then (if a = c then
            (p * (ga 1 * gb 1 * gc 1 * gd 1) + (1 - p) * (ga 0 * gb 0 * gc 0 * gd 0))
          else (p * (ga 1 * gb 1) + (1 - p) * (ga 0 * gb 0))
                * (p * (gc 1 * gd 1) + (1 - p) * (gc 0 * gd 0)))
        else 0)
      else (if a = c then (if b = d then
            (p * (ga 1 * gc 1) + (1 - p) * (ga 0 * gc 0))
              * (p * (gb 1 * gd 1) + (1 - p) * (gb 0 * gd 0))
          else 0)
        else (if a = d then (if b = c then
            (p * (ga 1 * gd 1) + (1 - p) * (ga 0 * gd 0))
              * (p * (gb 1 * gc 1) + (1 - p) * (gb 0 * gc 0))
          else 0)
        else 0))) := by
  classical
  rw [four_coord_factor p a b c d ga gb gc gd]
  set lf : (Fin n₁ × Fin n₂) → ℝ := fun u =>
        (p * ((if a = u then ga 1 else 1) * (if b = u then gb 1 else 1)
              * (if c = u then gc 1 else 1) * (if d = u then gd 1 else 1))
         + (1 - p) * ((if a = u then ga 0 else 1) * (if b = u then gb 0 else 1)
              * (if c = u then gc 0 else 1) * (if d = u then gd 0 else 1))) with hlf
  -- lf at a lone "a"-index (b,c,d ≠ that index) reduces to ga's mean = 0
  have lone_a : ∀ u, a = u → b ≠ u → c ≠ u → d ≠ u → lf u = 0 := by
    intro u hau hbu hcu hdu
    simp only [hlf, if_pos hau, if_neg hbu, if_neg hcu, if_neg hdu, mul_one]
    linarith [hma]
  have lone_b : ∀ u, b = u → a ≠ u → c ≠ u → d ≠ u → lf u = 0 := by
    intro u hbu hau hcu hdu
    simp only [hlf, if_pos hbu, if_neg hau, if_neg hcu, if_neg hdu, mul_one, one_mul]
    linarith [hmb]
  have lone_c : ∀ u, c = u → a ≠ u → b ≠ u → d ≠ u → lf u = 0 := by
    intro u hcu hau hbu hdu
    simp only [hlf, if_pos hcu, if_neg hau, if_neg hbu, if_neg hdu, mul_one, one_mul]
    linarith [hmc]
  have lone_d : ∀ u, d = u → a ≠ u → b ≠ u → c ≠ u → lf u = 0 := by
    intro u hdu hau hbu hcu
    simp only [hlf, if_pos hdu, if_neg hau, if_neg hbu, if_neg hcu, mul_one, one_mul]
    linarith [hmd]
  have val_all : ∀ u, a = u → b = u → c = u → d = u →
      lf u = p * (ga 1 * gb 1 * gc 1 * gd 1) + (1 - p) * (ga 0 * gb 0 * gc 0 * gd 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_pos h3, if_pos h4]
  have val_ab : ∀ u, a = u → b = u → c ≠ u → d ≠ u →
      lf u = p * (ga 1 * gb 1) + (1 - p) * (ga 0 * gb 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, mul_one]
  have val_cd : ∀ u, c = u → d = u → a ≠ u → b ≠ u →
      lf u = p * (gc 1 * gd 1) + (1 - p) * (gc 0 * gd 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, one_mul]
  have val_ac : ∀ u, a = u → c = u → b ≠ u → d ≠ u →
      lf u = p * (ga 1 * gc 1) + (1 - p) * (ga 0 * gc 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, mul_one]
  have val_bd : ∀ u, b = u → d = u → a ≠ u → c ≠ u →
      lf u = p * (gb 1 * gd 1) + (1 - p) * (gb 0 * gd 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, one_mul, mul_one]
  have val_ad : ∀ u, a = u → d = u → b ≠ u → c ≠ u →
      lf u = p * (ga 1 * gd 1) + (1 - p) * (ga 0 * gd 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, mul_one]
  have val_bc : ∀ u, b = u → c = u → a ≠ u → d ≠ u →
      lf u = p * (gb 1 * gc 1) + (1 - p) * (gb 0 * gc 0) := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_pos h1, if_pos h2, if_neg h3, if_neg h4, one_mul, mul_one]
  have val_one : ∀ u, a ≠ u → b ≠ u → c ≠ u → d ≠ u → lf u = 1 := by
    intro u h1 h2 h3 h4
    simp only [hlf, if_neg h1, if_neg h2, if_neg h3, if_neg h4, mul_one]
    ring
  have prod_single : ∀ u : Fin n₁ × Fin n₂,
      (∀ v, v ≠ u → lf v = 1) → (∏ w : Fin n₁ × Fin n₂, lf w) = lf u := by
    intro u hv
    rw [← Finset.prod_subset (Finset.subset_univ {u})]
    · simp
    · intro v _ hv2; apply hv; simpa using hv2
  have prod_pair : ∀ u v : Fin n₁ × Fin n₂, u ≠ v →
      (∀ w, w ≠ u → w ≠ v → lf w = 1) →
      (∏ w : Fin n₁ × Fin n₂, lf w) = lf u * lf v := by
    intro u v huv hw
    rw [← Finset.prod_subset (Finset.subset_univ {u, v})]
    · rw [Finset.prod_pair huv]
    · intro w _ hw2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw2
      exact hw w hw2.1 hw2.2
  -- 64-way case split, following the RHS if-structure (no subst).
  by_cases hab : a = b
  · by_cases hcd : c = d
    · by_cases hac : a = c
      · simp only [if_pos hab, if_pos hcd, if_pos hac]
        rw [prod_single a (fun v hv => val_one v (by grind) (by grind) (by grind) (by grind))]
        rw [val_all a rfl (by grind) (by grind) (by grind)]
      · simp only [if_pos hab, if_pos hcd, if_neg hac]
        rw [prod_pair a c hac (fun w hwa hwc => val_one w (by grind) (by grind) (by grind) (by grind))]
        rw [val_ab a rfl (by grind) (by grind) (by grind),
            val_cd c rfl (by grind) (by grind) (by grind)]
    · simp only [if_pos hab, if_neg hcd]
      by_cases hca : c = a
      · rw [Finset.prod_eq_zero (Finset.mem_univ d)
          (lone_d d rfl (by grind) (by grind) (by grind))]
      · rw [Finset.prod_eq_zero (Finset.mem_univ c)
          (lone_c c rfl (by grind) (by grind) (by grind))]
  · by_cases hac : a = c
    · by_cases hbd : b = d
      · simp only [if_neg hab, if_pos hac, if_pos hbd]
        rw [prod_pair a b (by grind) (fun w hwa hwb => val_one w (by grind) (by grind) (by grind) (by grind))]
        rw [val_ac a rfl (by grind) (by grind) (by grind),
            val_bd b rfl (by grind) (by grind) (by grind)]
      · simp only [if_neg hab, if_pos hac, if_neg hbd]
        by_cases hba : b = a
        · rw [Finset.prod_eq_zero (Finset.mem_univ d)
            (lone_d d rfl (by grind) (by grind) (by grind))]
        · rw [Finset.prod_eq_zero (Finset.mem_univ b)
            (lone_b b rfl (by grind) (by grind) (by grind))]
    · by_cases had : a = d
      · by_cases hbc : b = c
        · simp only [if_neg hab, if_neg hac, if_pos had, if_pos hbc]
          rw [prod_pair a b (by grind) (fun w hwa hwb => val_one w (by grind) (by grind) (by grind) (by grind))]
          rw [val_ad a rfl (by grind) (by grind) (by grind),
              val_bc b rfl (by grind) (by grind) (by grind)]
        · simp only [if_neg hab, if_neg hac, if_pos had, if_neg hbc]
          by_cases hba : b = a
          · rw [Finset.prod_eq_zero (Finset.mem_univ c)
              (lone_c c rfl (by grind) (by grind) (by grind))]
          · rw [Finset.prod_eq_zero (Finset.mem_univ b)
              (lone_b b rfl (by grind) (by grind) (by grind))]
      · simp only [if_neg hab, if_neg hac, if_neg had]
        rw [Finset.prod_eq_zero (Finset.mem_univ a)
          (lone_a a rfl (by grind) (by grind) (by grind))]

/-- **Per-term value of the fourth-moment expansion.** For the centered term
`h_w(x) = p⁻¹ B_w (x − p)` (so the per-coordinate mean `μ₁ w = 0`), the four-fold
expectation `E[h_a h_b h_c h_d]` equals the product over the *distinct* indices of
the raw moment of the corresponding multiplicity. Because the mean is zero, only
the all-equal pattern (→ μ₄) and the two-distinct-pairs patterns (→ μ₂·μ₂) survive;
all patterns with a multiplicity-one index vanish. This is the explicit
**combinatorial partition lemma** for `q = 4`. -/
private theorem term_value {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (a b c d : Fin n₁ × Fin n₂) :
    bernoulliExpectation p
        (fun Omega =>
          (p⁻¹ * (B a.1 a.2) * ((if a ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B b.1 b.2) * ((if b ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B c.1 c.2) * ((if c ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B d.1 d.2) * ((if d ∈ Omega then 1 else 0) - p))) =
      (if a = b then (if c = d then (if a = c then
            -- all four equal: μ₄
            (p * (p⁻¹ * (B a.1 a.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B a.1 a.2) * (0 - p))^4)
          else
            -- a=b, c=d, a≠c: μ₂(a)·μ₂(c)
            (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B c.1 c.2)^2))
        else 0)
      else (if a = c then (if b = d then
            -- a=c, b=d, a≠b: μ₂(a)·μ₂(b)
            (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2)
          else 0)
        else (if a = d then (if b = c then
            -- a=d, b=c, a≠b: μ₂(a)·μ₂(b)
            (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2)
          else 0)
        else 0))) := by
  classical
  -- mean-zero of each centered coordinate function
  have hm : ∀ w : Fin n₁ × Fin n₂,
      p * (p⁻¹ * (B w.1 w.2) * ((1:ℝ) - p)) + (1 - p) * (p⁻¹ * (B w.1 w.2) * ((0:ℝ) - p)) = 0 := by
    intro w; field_simp; ring
  rw [four_coord_eval p a b c d
        (fun x => p⁻¹ * (B a.1 a.2) * (x - p))
        (fun x => p⁻¹ * (B b.1 b.2) * (x - p))
        (fun x => p⁻¹ * (B c.1 c.2) * (x - p))
        (fun x => p⁻¹ * (B d.1 d.2) * (x - p))
        (hm a) (hm b) (hm c) (hm d)]
  -- bridge the abstract factorized value to the concrete closed forms; the two
  -- if-structures coincide branch-by-branch.
  by_cases hab : a = b <;> by_cases hcd : c = d <;> by_cases hac : a = c <;>
    by_cases hbd : b = d <;> by_cases had : a = d <;> by_cases hbc : b = c <;>
    simp only [hab, hcd, hac, hbd, had, hbc, if_true, if_false] <;>
    (repeat (first
      | (rw [if_neg (by grind : ¬ (_ : Fin n₁ × Fin n₂) = _)])
      | (rw [if_pos (by grind : (_ : Fin n₁ × Fin n₂) = _)]))) <;>
    (try field_simp) <;> (try ring)

/-- `centered_sampling_coefficient_fourth_moment`.

**Exact fourth moment of the scalar centered sampling coefficient.** With
`Coeff Ω = ∑_{ij} p⁻¹(𝟙[(i,j)∈Ω]−p)B_{ij}` and `0 < p ≤ 1`,
$$\mathbb{E}[\mathrm{Coeff}^4]
   = \sum_w \mathbb{E}[h_w^4] + 3\sum_{a\ne b}\mathbb{E}[h_a^2]\,\mathbb{E}[h_b^2],$$
where `h_w(x)=p⁻¹B_w(x−p)`, `E[h_w^2]=((1-p)/p)B_w²` and
`E[h_w^4]=p⁻³((1-p)+(1-p)^3 p? )…` — concretely each per-coordinate fourth moment
is `p·h_w(1)^4+(1-p)·h_w(0)^4`. Proof (Boucheron–Lugosi–Massart, *Concentration
Inequalities*, OUP 2013, Ch. 15; Rosenthal 1970, *Israel J. Math.* 8, eq. for the
fourth moment of a sum of independent mean-zero variables): expand
`Coeff^4 = ∑_{a,b,c,d} h_a h_b h_c h_d`, push the expectation through all four
sums (quadruple linearity), and evaluate each term by independence. Every term in
which some index occurs with multiplicity exactly one carries a factor that is the
single-coordinate **mean** `p·h_w(1)+(1-p)·h_w(0)=0`, hence vanishes. The only
surviving index patterns are: all four equal (the `∑_w E[h_w^4]` diagonal) and two
distinct pairs (`3` orderings × `∑_{a≠b} E[h_a^2]E[h_b^2]`).

Collection of the per-term values into the diagonal + 3×cross closed form is the
`collect` lemma below; `solution` follows it. -/
private theorem collect {ι : Type*} [Fintype ι] [DecidableEq ι] (m4 : ι → ℝ) (mm : ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      (if a = b then (if c = d then (if a = c then m4 a else mm a c) else 0)
       else (if a = c then (if b = d then mm a b else 0)
             else (if a = d then (if b = c then mm a b else 0) else 0)))) =
    (∑ w, m4 w) + 3 * (∑ a, ∑ b, (if a = b then (0:ℝ) else mm a b)) := by
  have hT : ∀ a b c d : ι,
      (if a = b then (if c = d then (if a = c then m4 a else mm a c) else 0)
       else (if a = c then (if b = d then mm a b else 0)
             else (if a = d then (if b = c then mm a b else 0) else 0)))
      =
      ((if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0) * (if a = c then 1 else 0)) * m4 a
      + (if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0) * (if a = c then 0 else mm a c)
      + (if a = c then (1:ℝ) else 0) * (if b = d then 1 else 0) * (if a = b then 0 else mm a b)
      + (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0)
          * (if a = b then 0 else (if a = c then 0 else mm a b)) := by
    intro a b c d
    by_cases hab : a = b <;> by_cases hcd : c = d <;> by_cases hac : a = c <;>
      by_cases hbd : b = d <;> by_cases had : a = d <;> by_cases hbc : b = c <;>
      simp only [hab, hcd, hac, hbd, had, hbc, if_true, if_false] <;> ring_nf <;>
      grind
  simp only [hT]
  simp only [Finset.sum_add_distrib]
  have S1 : (∑ a, ∑ b, ∑ c, ∑ d : ι,
      ((if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0) * (if a = c then 1 else 0)) * m4 a)
      = ∑ w, m4 w := by
    apply Finset.sum_congr rfl; intro a _
    have step : ∀ b c, (∑ d : ι, ((if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0)
        * (if a = c then 1 else 0)) * m4 a) =
        ((if a = b then (1:ℝ) else 0) * (if a = c then 1 else 0)) * m4 a := by
      intro b c
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      simp [Finset.sum_ite_eq]
    simp only [step]
    rw [Finset.sum_comm]
    have step2 : ∀ c, (∑ b : ι, ((if a = b then (1:ℝ) else 0) * (if a = c then 1 else 0)) * m4 a)
        = ((if a = c then (1:ℝ) else 0)) * m4 a := by
      intro c
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      simp [Finset.sum_ite_eq]
    simp only [step2]
    rw [← Finset.sum_mul]
    simp [Finset.sum_ite_eq]
  have collapse2 : ∀ (g : ι → ι → ℝ),
      (∑ a, ∑ b, ∑ c, ∑ d : ι,
        (if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0) * g a c) =
      ∑ a, ∑ c, g a c := by
    intro g
    apply Finset.sum_congr rfl; intro a _
    have step : ∀ b c, (∑ d : ι, (if a = b then (1:ℝ) else 0) * (if c = d then 1 else 0) * g a c) =
        (if a = b then (1:ℝ) else 0) * g a c := by
      intro b c
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
      simp [Finset.sum_ite_eq]
    simp only [step]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    rw [← Finset.sum_mul]
    simp [Finset.sum_ite_eq]
  have collapse_ac_bd : ∀ (g : ι → ι → ℝ),
      (∑ a, ∑ b, ∑ c, ∑ d : ι,
        (if a = c then (1:ℝ) else 0) * (if b = d then 1 else 0) * g a b) =
      ∑ a, ∑ b, g a b := by
    intro g
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have step : ∀ c, (∑ d : ι, (if a = c then (1:ℝ) else 0) * (if b = d then 1 else 0) * g a b) =
        (if a = c then (1:ℝ) else 0) * g a b := by
      intro c
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
      simp [Finset.sum_ite_eq]
    simp only [step]
    rw [← Finset.sum_mul]
    simp [Finset.sum_ite_eq]
  have collapse_ad_bc : ∀ (g : ι → ι → ℝ),
      (∑ a, ∑ b, ∑ c, ∑ d : ι,
        (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0) * g a b) =
      ∑ a, ∑ b, g a b := by
    intro g
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have step : ∀ c, (∑ d : ι, (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0) * g a b) =
        (if b = c then (1:ℝ) else 0) * g a b := by
      intro c
      rw [show (∑ d : ι, (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0) * g a b)
          = (if b = c then (1:ℝ) else 0) * g a b * (∑ d : ι, (if a = d then (1:ℝ) else 0)) from ?_]
      · simp [Finset.sum_ite_eq]
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
    simp only [step]
    rw [← Finset.sum_mul]
    simp [Finset.sum_ite_eq]
  rw [S1, collapse2 (fun a c => if a = c then 0 else mm a c)]
  rw [collapse_ac_bd (fun a b => if a = b then 0 else mm a b)]
  rw [show (∑ a, ∑ b, ∑ c, ∑ d : ι,
      (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0)
        * (if a = b then 0 else if a = c then 0 else mm a b))
      = ∑ a, ∑ b, ∑ c, ∑ d : ι,
      (if a = d then (1:ℝ) else 0) * (if b = c then 1 else 0)
        * (if a = b then 0 else mm a b) from ?_]
  · rw [collapse_ad_bc (fun a b => if a = b then 0 else mm a b)]
    ring
  · apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    by_cases hbc : b = c
    · by_cases hab : a = b <;> simp [hbc, hab] <;> grind
    · simp [hbc]

theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 4) =
      (∑ w : Fin n₁ × Fin n₂,
          (p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4))
      + 3 * (∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
          (if a = b then 0 else
            (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2))) := by
  classical
  -- Step 1: rewrite the integrand as a fourfold sum of products of centered terms.
  have hint : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 4) =
      (fun Omega => ∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
        ∑ c : Fin n₁ × Fin n₂, ∑ d : Fin n₁ × Fin n₂,
        ((p⁻¹ * (B a.1 a.2) * ((if a ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B b.1 b.2) * ((if b ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B c.1 c.2) * ((if c ∈ Omega then 1 else 0) - p))
          * (p⁻¹ * (B d.1 d.2) * ((if d ∈ Omega then 1 else 0) - p)))) := by
    funext Omega
    rw [coeff_eq_linear p B Omega]
    rw [show (∑ w : Fin n₁ × Fin n₂, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p))) ^ 4
          = (∑ w : Fin n₁ × Fin n₂, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)))
            * (∑ w, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)))
            * (∑ w, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)))
            * (∑ w, (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p))) by ring]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [hint]
  -- Step 2: push the expectation through all four sums (quadruple linearity).
  rw [bernoulli_powerset_expectation_quadruple p
        (fun a b c d xa xb xc xd =>
          (p⁻¹ * (B a.1 a.2) * (xa - p)) * (p⁻¹ * (B b.1 b.2) * (xb - p))
            * (p⁻¹ * (B c.1 c.2) * (xc - p)) * (p⁻¹ * (B d.1 d.2) * (xd - p)))]
  -- Step 3: evaluate each term by independence (term_value).
  simp only [term_value p hp B]
  -- Step 4: collect into the diagonal + 3×cross closed form.
  have hcol := collect (ι := Fin n₁ × Fin n₂)
        (fun w => p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4)
        (fun a b => (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2))
  simp only [] at hcol
  convert hcol using 2
