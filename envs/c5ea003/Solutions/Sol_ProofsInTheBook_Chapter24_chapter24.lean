-- Prove2me | solution 1 for ProofsInTheBook.Chapter24.chapter24
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:13:02.512475+00:00
-- url     : https://prove2.me/submissions/0514dbd4-d924-4c31-8f2c-1f868427a5f6

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter24


/-!
# Chapter 24: Cotangent and the Herglotz trick

From "Proofs from THE BOOK":

**Herglotz trick**: The partial fraction expansion
π·cot(πx) = 1/x + ∑_{n=1}^∞ (1/(x+n) + 1/(x-n))
is proved by showing both sides satisfy the same functional equation
f(x) + f(1-x) = ... and f(x+1) = f(x), with matching initial conditions.

Applications include the Basel problem (Chapter 8) and evaluation of
the Riemann zeta function at even integers.
-/

namespace ProofsInTheBook.Chapter24

open scoped BigOperators











/--
Abstract Herglotz cancellation: period one plus oddness forces the
`x ↦ 1 - x` symmetry.
-/
theorem herglotz_cancel_of_periodic_odd (f : ℝ → ℝ)
    (hper : ∀ x, f (x + 1) = f x) (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    f (1 - x) = -f x := by
  have harg : 1 - x = -x + 1 := by ring
  calc
    f (1 - x) = f (-x + 1) := by rw [harg]
    _ = f (-x) := hper (-x)
    _ = -f x := hodd x

theorem herglotz_add_cancel_of_periodic_odd (f : ℝ → ℝ)
    (hper : ∀ x, f (x + 1) = f x) (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    f x + f (1 - x) = 0 := by
  rw [herglotz_cancel_of_periodic_odd f hper hodd x]
  ring





theorem HerglotzClass.cancel {f : ℝ → ℝ} (hf : HerglotzClass f) (x : ℝ) :
    f x + f (1 - x) = 0 :=
  herglotz_add_cancel_of_periodic_odd f hf.periodic hf.odd x

theorem HerglotzClass.eval_half {f : ℝ → ℝ} (hf : HerglotzClass f) : f (1/2) = 0 := by
  have h := hf.cancel (1/2)
  have : 1 - 1 / 2 = (1 : ℝ) / 2 := by ring
  rw [this] at h
  linarith













/--
Helper: if h achieves max M at x₀ and h(x₀) = (1/2)(h(x₀/2) + h((x₀+1)/2)) with
both ≤ M, then h(x₀/2) = M.
-/
private theorem avg_eq_max_implies_both_eq (a b M : ℝ) (ha : a ≤ M) (hb : b ≤ M)
    (havg : M = (1/2 : ℝ) * (a + b)) : a = M ∧ b = M := by
  constructor <;> nlinarith

/--
Key lemma: a continuous periodic function satisfying duplication with h(0) = 0
that achieves its max must have max ≤ 0.
-/
private theorem max_le_zero_of_dup_zero
    (h : ℝ → ℝ) (hcont : Continuous h) (_hper : ∀ x, h (x + 1) = h x)
    (hdup : ∀ x, h x = (1/2 : ℝ) * (h (x/2) + h ((x+1)/2)))
    (hzero : h 0 = 0)
    (x₀ : ℝ) (hmax : ∀ y, h y ≤ h x₀) : h x₀ ≤ 0 := by
  by_contra hpos; push Not at hpos
  have hiter : ∀ n : ℕ, h (x₀ / 2 ^ n) = h x₀ := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      have hd := hdup (x₀ / 2 ^ n)
      rw [ih] at hd
      have := avg_eq_max_implies_both_eq
        (h (x₀ / 2 ^ n / 2)) (h ((x₀ / 2 ^ n + 1) / 2)) (h x₀)
        (hmax _) (hmax _) hd
      rw [show x₀ / (2 : ℝ) ^ n / 2 = x₀ / (2 : ℝ) ^ (n + 1) from by ring] at this
      exact this.1
  have hlim : Filter.Tendsto (fun n : ℕ => x₀ / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have h12 : Filter.Tendsto (fun n : ℕ => (1 / (2 : ℝ)) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have := h12.const_mul x₀
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div, inv_pow]; ring
  have hconv := (hcont.tendsto 0).comp hlim
  have : Filter.Tendsto (fun n => h (x₀ / 2 ^ n)) Filter.atTop (nhds (h 0)) := hconv
  have hconst : Filter.Tendsto (fun n => h (x₀ / 2 ^ n)) Filter.atTop (nhds (h x₀)) := by
    rw [show (fun n => h (x₀ / 2 ^ n)) = fun _ => h x₀ from funext hiter]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst this
  linarith

/--
The Herglotz uniqueness theorem (the book's key argument): if two functions
in the Herglotz class (periodic-one, odd) are both continuous and satisfy the
same duplication formula, then they agree everywhere. The proof uses the
duplication to show the difference function `h = f - g` satisfies
`h(x) = (1/2^n) · ∑ h(...)` for all n, forcing `h = 0` by boundedness.
-/
theorem herglotz_uniqueness_of_continuous_periodic_odd
    (f g : ℝ → ℝ) (hf : HerglotzClass f) (hg : HerglotzClass g)
    (hfc : Continuous f) (hgc : Continuous g)
    (hdup_f : ∀ x, 2 * f x = f (x / 2) + f ((x + 1) / 2))
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (_hhalf : f (1/2) = g (1/2)) :
    f = g := by
  suffices ∀ x, f x - g x = 0 by ext x; linarith [this x]
  let d := fun x => f x - g x
  have dcont : Continuous d := hfc.sub hgc
  have dper : ∀ x, d (x + 1) = d x := fun x => by
    simp only [d]; linarith [hf.periodic x, hg.periodic x]
  have dcancel : ∀ x, d x + d (1 - x) = 0 := fun x => by
    simp only [d]; linarith [hf.cancel x, hg.cancel x]
  have dperiodic : Function.Periodic d 1 := fun x => dper x
  have dper_int : ∀ (y : ℝ), d (y - ↑⌊y⌋ * 1) = d y := by
    intro y; exact dperiodic.sub_int_mul_eq ⌊y⌋
  have dred : ∀ y, ∃ z ∈ Set.Icc (0:ℝ) 1, d y = d z := by
    intro y
    refine ⟨Int.fract y, ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩, ?_⟩
    have : d (Int.fract y) = d y := by
      simp only [Int.fract]
      convert dperiodic.sub_int_mul_eq ⌊y⌋ using 2; ring
    exact this.symm
  have ddup : ∀ x, d x = (1/2 : ℝ) * (d (x/2) + d ((x+1)/2)) := fun x => by
    simp only [d]; have := hdup_f x; have := hdup_g x; linarith
  have dzero : d 0 = 0 := by
    have h1 : d 0 + d 1 = 0 := by convert dcancel 0 using 2; ring_nf
    have h2 : d 1 = d 0 := by convert dper 0 using 2; ring
    linarith
  intro x
  have hle : d x ≤ 0 := by
    by_contra hgt; push Not at hgt
    have hmax_exists : ∃ x₀, ∀ y, d y ≤ d x₀ := by
      obtain ⟨x₀, _, hx₀⟩ := IsCompact.exists_isMaxOn isCompact_Icc
        (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) dcont.continuousOn
      exact ⟨x₀, fun y => by obtain ⟨z, hz, heq⟩ := dred y; rw [heq]; exact hx₀ hz⟩
    obtain ⟨x₀, hx₀⟩ := hmax_exists
    exact absurd (max_le_zero_of_dup_zero d dcont dper ddup dzero x₀ hx₀) (by linarith [hx₀ x])
  have hge : 0 ≤ d x := by
    by_contra hlt; push Not at hlt
    have hmax_neg : ∃ x₀, ∀ y, -d y ≤ -d x₀ := by
      obtain ⟨x₀, _, hx₀⟩ := IsCompact.exists_isMinOn isCompact_Icc
        (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) dcont.continuousOn
      exact ⟨x₀, fun y => by obtain ⟨z, hz, heq⟩ := dred y; simp; rw [heq]; exact hx₀ hz⟩
    obtain ⟨x₀, hx₀⟩ := hmax_neg
    have := max_le_zero_of_dup_zero (fun y => -d y) dcont.neg
      (fun y => by show -d (y + 1) = -d y; linarith [dper y])
      (fun y => by show -d y = (1/2) * (-d (y/2) + -d ((y+1)/2)); linarith [ddup y])
      (by show -d 0 = 0; linarith [dzero]) x₀ hx₀
    linarith [hx₀ x]
  linarith











































end ProofsInTheBook.Chapter24

open scoped BigOperators
open ProofsInTheBook.Chapter24

theorem solution {f g : ℝ → ℝ}
    (hf : HerglotzClass f) (hg : HerglotzClass g)
    (hfc : Continuous f) (hgc : Continuous g)
    (hdup_f : ∀ x, 2 * f x = f (x / 2) + f ((x + 1) / 2))
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (x : ℝ) : f x = g x := by
  have heq : f = g :=
    herglotz_uniqueness_of_continuous_periodic_odd f g hf hg hfc hgc hdup_f hdup_g
      (by rw [hf.eval_half, hg.eval_half])
  rw [heq]
