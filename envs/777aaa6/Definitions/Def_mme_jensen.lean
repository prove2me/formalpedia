-- Prove2me | Definitions.Def_mme_jensen
-- name    : mme_jensen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:32:41.86739+00:00
-- url     : https://prove2.me/theorems/7ad0ecb4-9d09-4965-a515-76904f548283
-- statement:
--   **Convexity, Jensen averaging over the symmetric group $S_3$, and the Erdős–Hewitt lemma.**
--
--   Self-contained analytic ingredients for Strassen's $\tau$-theorem, adapted from the Prism `MatrixMult` development. None of these depend on the tensor machinery; the whole file is sorry-free.
--
--   **Convexity of the multi-power sum.** `sum_rpow_convex`:
--   $$F(x, y, z) = \sum_i n_i^x m_i^y p_i^z$$
--   is convex on $\mathbb{R}^3$ when each $n_i, m_i, p_i > 0$.
--
--   **Cyclic averaging.** `cyclicPerm3` is the order-3 permutation of $\mathrm{Fin}\,3$ and `permuteTriple` is its action on a real triple $(a,b,c) \mapsto (b,c,a)$. `jensen_S3_convex` applies Jensen to the average over the cyclic orbit: for a convex function $\Phi : \mathbb{R}^3 \to \mathbb{R}$ and any $\theta \in \mathbb{R}^3$,
--   $$\Phi\bigl(\bar\theta,\bar\theta,\bar\theta\bigr) \;\leq\; \tfrac{1}{3}\bigl(\Phi(\theta) + \Phi(\sigma\theta) + \Phi(\sigma^2\theta)\bigr), \quad \bar\theta = \tfrac{\theta_1+\theta_2+\theta_3}{3}.$$
--   This is the algebraic engine that converts a per-spectrum-point inequality with three distinct exponents into one with the symmetric $\omega/3$ exponent.
--
--   **Erdős–Hewitt.** `mono_mult_eq_rpow`: every monotone multiplicative function $\mathbb{N} \to \mathbb{R}_{\geq 0}$ that takes the value $1$ on $1$ is a power function $n \mapsto n^\alpha$ for some $\alpha \geq 0$. This characterization lets `Def_mme_mm_spectral`'s `MM_eval` API extract the three coordinate exponents $\theta_1, \theta_2, \theta_3$ from a spectrum point.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation

/-! # Convexity, Jensen averaging over `S₃`, and the Erdős–Hewitt lemma (MME)

Self-contained analytic ingredients of Strassen's `τ` theorem, adapted from the Prism
`MatrixMult.lean`. None of these depend on the tensor machinery, and all are sorry-free:

* `sum_rpow_convex` — `v ↦ ∑ᵢ nᵢ^v₁ mᵢ^v₂ pᵢ^v₃` is convex on `ℝ³`;
* `cyclicPerm3` and `permuteTriple` — the cyclic permutation of `Fin 3` and its action
  on a real triple;
* `jensen_S3_convex` — Jensen averaging over the 3-cycle orbit;
* `mono_mult_eq_rpow` — the Erdős–Hewitt characterization of monotone multiplicative
  functions on `ℕ` as power functions. -/

universe u

open BigOperators

namespace MME

/-! ## Convexity of the multi-power sum -/

/-- The function `F(x,y,z) = ∑ i, nᵢˣ · mᵢʸ · pᵢᶻ` is convex on `ℝ³`. -/
theorem sum_rpow_convex {ι : Type*} [Fintype ι]
    (n m p : ι → ℝ) (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i) (hp : ∀ i, 0 < p i) :
    ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      ∑ i, (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
  let L : ι → (ℝ × ℝ × ℝ →ₗ[ℝ] ℝ) := fun i =>
    { toFun := fun v => v.1 * Real.log (n i) + v.2.1 * Real.log (m i) +
        v.2.2 * Real.log (p i)
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  have hg_eq : ∀ i (v : ℝ × ℝ × ℝ),
      (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2 = Real.exp (L i v) := by
    intro i v
    show (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2 =
      Real.exp (v.1 * Real.log (n i) + v.2.1 * Real.log (m i) + v.2.2 * Real.log (p i))
    rw [Real.rpow_def_of_pos (hn i), Real.rpow_def_of_pos (hm i),
        Real.rpow_def_of_pos (hp i)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hg_convex : ∀ i, ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
    intro i
    have h_comp : ConvexOn ℝ ((L i) ⁻¹' Set.univ) (Real.exp ∘ (L i)) :=
      convexOn_exp.comp_linearMap (L i)
    have hpre : (L i) ⁻¹' (Set.univ : Set ℝ) = Set.univ := by ext x; simp
    rw [hpre] at h_comp
    convert h_comp using 1
    ext v; exact hg_eq i v
  have h_sum : ∀ s : Finset ι, ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      ∑ i ∈ s, (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
    intro s
    induction s using Finset.cons_induction_on with
    | empty => simp only [Finset.sum_empty]; exact convexOn_const _ convex_univ
    | cons _ _ _ ih => simp only [Finset.sum_cons]; exact (hg_convex _).add ih
  exact h_sum Finset.univ

/-! ## The cyclic permutation of `Fin 3` and its action on triples -/

/-- The cyclic permutation of `Fin 3`: `0 ↦ 1 ↦ 2 ↦ 0`. -/
def cyclicPerm3 : Equiv.Perm (Fin 3) where
  toFun
    | ⟨0, _⟩ => ⟨1, by norm_num⟩
    | ⟨1, _⟩ => ⟨2, by norm_num⟩
    | ⟨2, _⟩ => ⟨0, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  invFun
    | ⟨0, _⟩ => ⟨2, by norm_num⟩
    | ⟨1, _⟩ => ⟨0, by norm_num⟩
    | ⟨2, _⟩ => ⟨1, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv := by decide
  right_inv := by decide

/-- Apply a permutation of `Fin 3` to a triple `(ℝ × ℝ × ℝ)`, viewed as `Fin 3 → ℝ`. -/
noncomputable def permuteTriple (σ : Equiv.Perm (Fin 3)) (θ : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let f : Fin 3 → ℝ := ![θ.1, θ.2.1, θ.2.2]
  (f (σ.symm ⟨0, by norm_num⟩), f (σ.symm ⟨1, by norm_num⟩), f (σ.symm ⟨2, by norm_num⟩))

/-! ## Jensen averaging over the 3-cycle orbit -/

/-- Jensen's inequality applied over the cyclic `S₃`-orbit: if `f` is convex and
`f(permuteTriple σ θ) ≤ r` for the three cyclic powers `σ`, then `f` at the barycenter
of the orbit (all coordinates `(a+b+c)/3`) is also `≤ r`. -/
theorem jensen_S3_convex {f : ℝ × ℝ × ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (θ : ℝ × ℝ × ℝ)
    (r : ℝ) (hσ : ∀ σ ∈ ({Equiv.refl _, cyclicPerm3, cyclicPerm3 * cyclicPerm3} :
        Set (Equiv.Perm (Fin 3))), f (permuteTriple σ θ) ≤ r) :
    f ((θ.1 + θ.2.1 + θ.2.2) / 3, (θ.1 + θ.2.1 + θ.2.2) / 3,
       (θ.1 + θ.2.1 + θ.2.2) / 3) ≤ r := by
  set a := θ.1
  set b := θ.2.1
  set c := θ.2.2
  have h_id : permuteTriple (Equiv.refl _) θ = (a, b, c) := rfl
  have h_cyc : permuteTriple cyclicPerm3 θ = (c, a, b) := rfl
  have h_cyc2 : permuteTriple (cyclicPerm3 * cyclicPerm3) θ = (b, c, a) := rfl
  have h1 : f (a, b, c) ≤ r := h_id ▸ hσ (Equiv.refl _) (by simp)
  have h2 : f (c, a, b) ≤ r := h_cyc ▸ hσ cyclicPerm3 (by simp)
  have h3 : f (b, c, a) ≤ r := h_cyc2 ▸ hσ (cyclicPerm3 * cyclicPerm3) (by simp)
  have h_avg_pt : ((a + b + c) / 3, (a + b + c) / 3, (a + b + c) / 3) =
      (1/3 : ℝ) • (a, b, c) + (1/3 : ℝ) • (c, a, b) + (1/3 : ℝ) • (b, c, a) := by
    show (((a + b + c) / 3 : ℝ), ((a + b + c) / 3 : ℝ), ((a + b + c) / 3 : ℝ)) = _
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩ <;> ring
  rw [h_avg_pt]
  have h12 : (1/3 : ℝ) • (a, b, c) + (1/3 : ℝ) • (c, a, b) =
      (2/3 : ℝ) • ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) := by
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩ <;> ring
  rw [h12]
  have hf_at_M : f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) ≤ r := by
    have := hf.2 (Set.mem_univ (a, b, c)) (Set.mem_univ (c, a, b))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    calc f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b))
        ≤ (1/2 : ℝ) • f (a, b, c) + (1/2 : ℝ) • f (c, a, b) := this
      _ ≤ (1/2 : ℝ) • r + (1/2 : ℝ) • r := by gcongr
      _ = r := by simp; ring
  have h_two_step :=
    hf.2 (Set.mem_univ ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)))
      (Set.mem_univ (b, c, a))
      (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (2/3 : ℝ) + 1/3 = 1)
  calc f ((2/3 : ℝ) • ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) + (1/3 : ℝ) • (b, c, a))
      ≤ (2/3 : ℝ) • f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) +
          (1/3 : ℝ) • f (b, c, a) := h_two_step
    _ ≤ (2/3 : ℝ) • r + (1/3 : ℝ) • r := by gcongr
    _ = r := by simp; ring

/-! ## Erdős–Hewitt: monotone multiplicative functions are power functions -/

/-- For real-valued `f` multiplicative, `f 1 = 1`, monotone, `1 ≤ f n` for `n ≥ 1`, and
polynomially bounded, the squeeze gives `f n = n ^ (log f 2 / log 2)` for all `n ≥ 1`. -/
theorem mono_mult_eq_rpow (f : ℕ → ℝ)
    (h_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b)
    (h_one : f 1 = 1)
    (h_mono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f a ≤ f b)
    (h_one_le : ∀ a : ℕ, 1 ≤ a → 1 ≤ f a)
    (_h_le_n : ∀ a : ℕ, 1 ≤ a → f a ≤ a) :
    ∀ n : ℕ, 1 ≤ n → f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  set α := Real.log (f 2) / Real.log 2 with hα_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf2_pos : 0 < f 2 := lt_of_lt_of_le zero_lt_one (h_one_le 2 (by norm_num))
  have hf2_ge_one : 1 ≤ f 2 := h_one_le 2 (by norm_num)
  have hlogf2_nonneg : 0 ≤ Real.log (f 2) := Real.log_nonneg hf2_ge_one
  have h_pow : ∀ (n k : ℕ), 1 ≤ n → f (n ^ k) = f n ^ k := by
    intro n k hn
    induction k with
    | zero => simp [h_one]
    | succ k ih =>
        rw [pow_succ, h_mul _ _ (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))) hn,
          ih, pow_succ]
  have hfn_pos : ∀ n : ℕ, 1 ≤ n → 0 < f n := fun n hn =>
    lt_of_lt_of_le zero_lt_one (h_one_le n hn)
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h1
  · rw [← h1, h_one]; simp
  have hn2 : 2 ≤ n := h1
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hfn_ge_one : 1 ≤ f n := h_one_le n (by omega)
  have hlogfn_nonneg : 0 ≤ Real.log (f n) := Real.log_nonneg hfn_ge_one
  set β := Real.log (f n) / Real.log n with hβ_def
  suffices h : β = α by
    have hlogeq : Real.log (f n) = α * Real.log n := by
      have := h ▸ hβ_def; field_simp at this; linarith
    have hfn_pos' : 0 < f n := hfn_pos n (by omega)
    have hthis : Real.log ((n : ℝ) ^ α) = Real.log (f n) := by
      rw [Real.log_rpow hn_real_pos, ← hlogeq]
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hn_real_pos _))
                                (Set.mem_Ioi.mpr hfn_pos') hthis
    exact this.symm
  by_cases hf2_eq : f 2 = 1
  · have hα_zero : α = 0 := by simp [hα_def, hf2_eq]
    have hfn_eq_one : f n = 1 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n ≤ 2 ^ k := ⟨n, Nat.lt_two_pow_self.le⟩
      have h_fle : f n ≤ f (2 ^ k) := h_mono _ _ (by omega) hk
      rw [h_pow 2 k (by norm_num), hf2_eq, one_pow] at h_fle
      linarith
    have hβ_zero : β = 0 := by simp [hβ_def, hfn_eq_one, Real.log_one]
    rw [hβ_zero, hα_zero]
  have hlogf2_pos : 0 < Real.log (f 2) := by
    apply lt_of_le_of_ne hlogf2_nonneg
    intro h
    apply hf2_eq
    have := Real.exp_log hf2_pos
    rw [← h, Real.exp_zero] at this
    exact this.symm
  have hα_pos : 0 < α := div_pos hlogf2_pos hlog2_pos
  have hsqueeze : ∀ k : ℕ, 1 ≤ k → |β - α| ≤ α / k := by
    intro k hk
    have hnk_pos : 0 < n ^ k := pow_pos hn_pos _
    set A := Nat.log 2 (n ^ k) with hA_def
    have hA_le : 2 ^ A ≤ n ^ k := Nat.pow_log_le_self 2 (by omega)
    have hA_lt : n ^ k < 2 ^ (A + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hA_le_real : (2 : ℝ) ^ A ≤ (n : ℝ) ^ k := by exact_mod_cast hA_le
    have hA_lt_real : (n : ℝ) ^ k < (2 : ℝ) ^ (A + 1) := by exact_mod_cast hA_lt
    have hlog_n_lo : (A : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log n := by
      have h1 : Real.log ((2 : ℝ) ^ A) ≤ Real.log ((n : ℝ) ^ k) :=
        Real.log_le_log (pow_pos (by norm_num) _) hA_le_real
      rwa [Real.log_pow, Real.log_pow] at h1
    have hlog_n_hi : (k : ℝ) * Real.log n ≤ ((A : ℝ) + 1) * Real.log 2 := by
      have h1 : Real.log ((n : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ (A + 1)) :=
        Real.log_le_log (pow_pos hn_real_pos _) hA_lt_real.le
      rw [Real.log_pow, Real.log_pow] at h1; push_cast at h1 ⊢; linarith
    have h_f_lo : f (2 ^ A) ≤ f (n ^ k) := h_mono _ _ (Nat.one_le_pow _ _ (by norm_num)) hA_le
    have h_f_hi : f (n ^ k) ≤ f (2 ^ (A + 1)) := h_mono _ _ (Nat.one_le_pow _ _ hn_pos) hA_lt.le
    rw [h_pow 2 A (by norm_num), h_pow n k (by omega)] at h_f_lo
    rw [h_pow n k (by omega), h_pow 2 (A + 1) (by norm_num)] at h_f_hi
    have hf2_pow_pos : ∀ j : ℕ, 0 < f 2 ^ j := fun j => pow_pos hf2_pos j
    have hfn_pow_pos : 0 < f n ^ k := pow_pos (hfn_pos n (by omega)) k
    have hlog_f_lo : (A : ℝ) * Real.log (f 2) ≤ (k : ℝ) * Real.log (f n) := by
      have h1 : Real.log (f 2 ^ A) ≤ Real.log (f n ^ k) :=
        Real.log_le_log (hf2_pow_pos A) h_f_lo
      rwa [Real.log_pow, Real.log_pow] at h1
    have hlog_f_hi : (k : ℝ) * Real.log (f n) ≤ ((A : ℝ) + 1) * Real.log (f 2) := by
      have h1 : Real.log (f n ^ k) ≤ Real.log (f 2 ^ (A + 1)) :=
        Real.log_le_log hfn_pow_pos h_f_hi
      rw [Real.log_pow, Real.log_pow] at h1; push_cast at h1 ⊢; linarith
    have k_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have habs : |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| ≤ 1 / k := by
      rw [abs_le]
      have hγ_lo : (A : ℝ) / k ≤ Real.log (f n) / Real.log (f 2) := by
        rw [div_le_div_iff₀ k_pos hlogf2_pos]; linarith
      have hγ_hi : Real.log (f n) / Real.log (f 2) ≤ ((A : ℝ) + 1) / k := by
        rw [div_le_div_iff₀ hlogf2_pos k_pos]; linarith
      have hα'_lo : (A : ℝ) / k ≤ Real.log n / Real.log 2 := by
        rw [div_le_div_iff₀ k_pos hlog2_pos]; linarith
      have hα'_hi : Real.log n / Real.log 2 ≤ ((A : ℝ) + 1) / k := by
        rw [div_le_div_iff₀ hlog2_pos k_pos]; linarith
      constructor
      · have : Real.log (f n) / Real.log (f 2) ≤ Real.log n / Real.log 2 + 1 / k := by
          calc Real.log (f n) / Real.log (f 2) ≤ ((A : ℝ) + 1) / k := hγ_hi
            _ = (A : ℝ) / k + 1 / k := by field_simp
            _ ≤ Real.log n / Real.log 2 + 1 / k := by linarith
        linarith
      · have : Real.log n / Real.log 2 ≤ Real.log (f n) / Real.log (f 2) + 1 / k := by
          calc Real.log n / Real.log 2 ≤ ((A : ℝ) + 1) / k := hα'_hi
            _ = (A : ℝ) / k + 1 / k := by field_simp
            _ ≤ Real.log (f n) / Real.log (f 2) + 1 / k := by linarith
        linarith
    have habs_β_α : |β - α| = |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| *
                              (Real.log (f 2) / Real.log n) := by
      have hβα : β - α = -(Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)) *
                          (Real.log (f 2) / Real.log n) := by
        rw [hβ_def, hα_def]; field_simp; ring
      rw [hβα, abs_mul, abs_neg, abs_of_pos (div_pos hlogf2_pos hlogn_pos)]
    rw [habs_β_α]
    have h1 : |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| *
                (Real.log (f 2) / Real.log n) ≤ (1 / k) * (Real.log (f 2) / Real.log n) :=
      mul_le_mul_of_nonneg_right habs (div_nonneg hlogf2_nonneg hlogn_pos.le)
    apply le_trans h1
    have hlog2_le_logn : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hkey : Real.log (f 2) / Real.log n ≤ Real.log (f 2) / Real.log 2 := by
      rw [div_le_div_iff₀ hlogn_pos hlog2_pos]
      have := mul_le_mul_of_nonneg_left hlog2_le_logn hlogf2_nonneg; linarith
    calc (1 / (k : ℝ)) * (Real.log (f 2) / Real.log n)
        ≤ (1 / (k : ℝ)) * (Real.log (f 2) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = α / k := by rw [hα_def]; ring
  by_contra hne
  have hdiff_pos : 0 < |β - α| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_gt (α / |β - α|)
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hk; push_cast at hk
      have : (0 : ℝ) < α / |β - α| := div_pos hα_pos hdiff_pos; linarith
    · exact h
  have hbound := hsqueeze k hk_pos
  have hk_pos_real : (0 : ℝ) < k := by exact_mod_cast hk_pos
  rw [div_lt_iff₀ hdiff_pos] at hk
  have hk_α : α / k < |β - α| := by rw [div_lt_iff₀ hk_pos_real]; linarith
  linarith

end MME


