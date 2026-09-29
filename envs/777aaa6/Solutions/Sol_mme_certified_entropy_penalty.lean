-- Prove2me | solution 1 for mme_certified_entropy_penalty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T21:22:20.995173+00:00
-- url     : https://prove2.me/submissions/794b83c2-f6a8-4380-bde2-0dc1abf3d4ad

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_entropy_penalty_of_positive_reference
open BigOperators MME MME.RegionRate MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.Cert

variable {half : ℕ} {parent : Fin 3 → ℕ}

/-- A coordinatewise weight, summed against a distribution, only sees that coordinate's marginal. -/
theorem sum_coord (p : RecursiveThinSplit.Split half parent → ℝ) (i : Fin 3) (L : Fin (half + 1) → ℝ) :
    ∑ c, p c * L (c.val i) =
      ∑ j, L j * mme_modern_marginal (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) p j := by
  classical
  rw [← Fintype.sum_fiberwise (fun a : RecursiveThinSplit.Split half parent ↦ a.val i)
    (fun c ↦ p c * L (c.val i))]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  unfold mme_modern_marginal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [a.property]
  ring

/-- Against a coordinatewise reference, the log-moment of a distribution depends only on its
marginals. -/
theorem log_moment (p : RecursiveThinSplit.Split half parent → ℝ) (hsum : ∑ c, p c = 1)
    (q : RecursiveThinSplit.Split half parent → ℝ) (L : Fin 3 → Fin (half + 1) → ℝ) (K : ℝ)
    (hlog : ∀ c, Real.log (q c) = (∑ i, L i (c.val i)) - K) :
    ∑ c, p c * Real.log (q c) =
      (∑ i, ∑ j, L i j * mme_modern_marginal (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) p j) - K := by
  classical
  have hstep : ∀ c : RecursiveThinSplit.Split half parent,
      p c * Real.log (q c) = (∑ i, p c * L i (c.val i)) - p c * K := by
    intro c
    rw [hlog c, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun c _ ↦ hstep c), Finset.sum_sub_distrib, Finset.sum_comm,
    ← Finset.sum_mul, hsum, one_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i _ ↦ sum_coord p i (L i))

/-- Upper bound on the entropy penalty from a coordinatewise positive reference. -/
theorem penalty_le (alpha : RecursiveThinSplit.Split half parent → ℝ)
    (hp : ∀ c, 0 ≤ alpha c) (hm : ∑ c, alpha c = 1)
    (q : RecursiveThinSplit.Split half parent → ℝ) (hq : ∀ c, 0 < q c) (hqm : ∑ c, q c = 1)
    (L : Fin 3 → Fin (half + 1) → ℝ) (K : ℝ)
    (hlog : ∀ c, Real.log (q c) = (∑ i, L i (c.val i)) - K) :
    Real.log 2 * entropyPenalty alpha ≤ -(∑ c, alpha c * Real.log (q c)) - entropy alpha := by
  refine mme_entropy_penalty_of_positive_reference alpha q hp hm hq hqm ?_
  intro rho hrho
  obtain ⟨hrp, hrm, hmarg⟩ := hrho
  rw [log_moment rho hrm q L K hlog, log_moment alpha hm q L K hlog]
  have : ∀ i : Fin 3, ∑ j, L i j *
      mme_modern_marginal (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) rho j =
      ∑ j, L i j *
        mme_modern_marginal (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) alpha j :=
    fun i ↦ Finset.sum_congr rfl (fun j _ ↦ by rw [hmarg i j])
  rw [Finset.sum_congr rfl (fun i _ ↦ this i)]

/-- Exponent vectors add under the reference value. -/
theorem qval_sum3 (E : Fin 3 → (Fin 4 → ℤ)) :
    qval (fun k ↦ ∑ i, E i k) = ∏ i, qval (E i) := by
  simp only [qval, Fin.sum_univ_three, Fin.prod_univ_three]
  rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_add₀ (by norm_num : (3:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (5:ℝ) ≠ 0), zpow_add₀ (by norm_num : (5:ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (7:ℝ) ≠ 0), zpow_add₀ (by norm_num : (7:ℝ) ≠ 0)]
  ring

/-- Upper bound on the entropy penalty from per-coordinate exponent vectors. -/
theorem penalty_le_coord (alpha : RecursiveThinSplit.Split half parent → ℝ)
    (hp : ∀ c, 0 ≤ alpha c) (hm : ∑ c, alpha c = 1)
    (E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ)) :
    Real.log 2 * entropyPenalty alpha ≤
      Real.log (∑ c : RecursiveThinSplit.Split half parent,
          qval (fun k ↦ ∑ i, E i (c.val i) k)) -
        (∑ c, alpha c * ∑ i, Real.log (qval (E i (c.val i)))) - entropy alpha := by
  classical
  set Z : ℝ := ∑ c : RecursiveThinSplit.Split half parent, qval (fun k ↦ ∑ i, E i (c.val i) k) with hZ
  have hne : Nonempty (RecursiveThinSplit.Split half parent) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    exact absurd hm (by norm_num)
  haveI := hne
  have hZpos : 0 < Z := by
    rw [hZ]
    exact Finset.sum_pos (fun c _ ↦ qval_pos _) Finset.univ_nonempty
  have hlogq : ∀ c : RecursiveThinSplit.Split half parent,
      Real.log (qval (fun k ↦ ∑ i, E i (c.val i) k) / Z) =
        (∑ i, Real.log (qval (E i (c.val i)))) - Real.log Z := by
    intro c
    rw [Real.log_div (qval_pos _).ne' hZpos.ne', qval_sum3 (fun i ↦ E i (c.val i)),
      Fin.prod_univ_three, Fin.sum_univ_three,
      Real.log_mul (mul_pos (qval_pos _) (qval_pos _)).ne' (qval_pos _).ne',
      Real.log_mul (qval_pos _).ne' (qval_pos _).ne']
  have hbound := penalty_le alpha hp hm
    (fun c ↦ qval (fun k ↦ ∑ i, E i (c.val i) k) / Z)
    (fun c ↦ div_pos (qval_pos _) hZpos)
    (by rw [← Finset.sum_div, ← hZ, div_self hZpos.ne'])
    (fun i j ↦ Real.log (qval (E i j))) (Real.log Z) hlogq
  refine le_trans hbound (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun c _ ↦ by rw [hlogq c] :
    ∀ c ∈ Finset.univ, alpha c * Real.log (qval (fun k ↦ ∑ i, E i (c.val i) k) / Z) =
      alpha c * ((∑ i, Real.log (qval (E i (c.val i)))) - Real.log Z))]
  rw [Finset.sum_congr rfl (fun c _ ↦ mul_sub (alpha c) _ _), Finset.sum_sub_distrib,
    ← Finset.sum_mul, hm, one_mul]
  ring

end MME.Cert

theorem solution :
    (∀ {half : ℕ} {parent : Fin 3 → ℕ} (p : RecursiveThinSplit.Split half parent → ℝ)
      (i : Fin 3) (L : Fin (half + 1) → ℝ),
      ∑ c, p c * L (c.val i) =
        ∑ j, L j * mme_modern_marginal
          (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) p j) ∧
    ∀ {half : ℕ} {parent : Fin 3 → ℕ} (alpha : RecursiveThinSplit.Split half parent → ℝ),
      (∀ c, 0 ≤ alpha c) → ∑ c, alpha c = 1 →
      ∀ E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ),
      Real.log 2 * entropyPenalty alpha ≤
        Real.log (∑ c : RecursiveThinSplit.Split half parent,
            qval (fun k ↦ ∑ i, E i (c.val i) k)) -
          (∑ c, alpha c * ∑ i, Real.log (qval (E i (c.val i)))) - entropy alpha :=
  ⟨fun {half} {parent} p i L ↦ MME.Cert.sum_coord p i L,
   fun {half} {parent} alpha hp hm E ↦ MME.Cert.penalty_le_coord alpha hp hm E⟩
