-- Prove2me | Definitions.Def_mme_duality
-- name    : mme_duality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T17:06:19.972754+00:00
-- url     : https://prove2.me/theorems/7c023867-44b6-4fec-a0e6-6c793e6ea75d
-- statement:
--   **Strassen duality and spectrum-nonemptiness for `MME.StrassenPreorder`.**
--
--   The two headline theorems of the abstract asymptotic-spectrum theory, ported from Wigderson–Zuiddam / the Prism `AsymptoticSpectra` development to the lightweight MME structures. Sorry-free.
--
--   **Spectrum-nonemptiness.** `mme_spectrum_nonempty`: every Strassen preorder $P$ has at least one asymptotic spectrum point. Proved by closing $P$ under asymptotic relaxation (`Def_mme_asymptotic_closure`), invoking Zorn's lemma to find a *maximal* closed extension (which is automatically *total* by `isMaximal_iff_isTotal_isClosed`), and applying `rho_toRingHom` (`Def_mme_fractional_rank`) on the total extension to extract a monotone semiring homomorphism $\varphi : R \to \mathbb{R}$ — i.e., a spectrum point.
--
--   **Strassen duality.** `mme_strassen_duality`:
--   $$\mathrm{asymptoticRank}_P(a) \;=\; \sup_{\varphi \,\in\, \mathrm{AsymptoticSpectrumPoint}(P)} \varphi(a).$$
--   One direction is easy (`StrassenPreorder.eval_le_asymptoticRank`: every spectrum point $\varphi$ is bounded by the asymptotic rank). The hard direction needs the spectrum to be "rich enough" to attain $\mathrm{asymptoticRank}_P(a)$ at some $\varphi$: for every $r < \mathrm{asymptoticRank}_P(a)$ there is a spectrum point $\varphi$ with $\varphi(a) > r$. The proof uses the maximal-extension construction at the specific obstruction $(a, r)$.
--
--   **Where used.** This is the analytic content powering `Def_mme_tensor_bridge`'s `bridge_omega` (which combines duality with compactness of the spectrum and the maximizing-point argument to identify $\omega_{\mathrm{abs}} = (\theta_1 + \theta_2 + \theta_3)(\varphi_{\max})$) and `Def_mme_mm_spectral`'s `MMData.sum_inequality`.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_mme_spectrum
import Definitions.Def_mme_asymptotic_closure
import Definitions.Def_mme_fractional_rank

/-! # Strassen duality and spectrum-nonemptiness for `MME.StrassenPreorder`

This file assembles the already-built MME machinery (rank facts and Fekete convergence
from `Def_mme_spectrum`, the asymptotic closure / total extension theory from
`Def_mme_asymptotic_closure`, and the fractional rank ring hom from
`Def_mme_fractional_rank`) into the two headline results of the abstract
asymptotic-spectrum theory:

* `mme_spectrum_nonempty`  — every Strassen preorder has at least one spectrum point;
* `mme_strassen_duality`   — `asymptoticRank P a = ⨆ φ, φ a` (Strassen's duality theorem).

The argument is ported from Wigderson–Zuiddam / the Prism `AsymptoticSpectra` development
(`Spectrum.lean`, `Duality.lean`), rewritten directly over the lightweight `MME`
structures. It is sorry-free. -/

universe u

noncomputable section

open Filter Topology
open scoped Classical

namespace MME

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R]

/-! ## In a total + closed preorder, `ρ` reflects the order

Ported from Prism `AsymptoticClosure.lean`'s `rho_reflects_le`; not present in the MME
`Def_mme_asymptotic_closure`, so we re-prove it here from `gap_property`, `rho_add`,
`rho_mul`, `rho_nat_cast`, `rho_one`, `rho_monotone`. -/

theorem rho_reflects_le (P : StrassenPreorder R) (h_total : P.IsTotal) (h_closed : P.IsClosed)
    (a b : R) : P.rho a ≤ P.rho b ↔ P.le a b := by
  constructor
  · intro h_rho
    by_contra h_not_le
    obtain ⟨m, hm_pos, hm_not_le⟩ := gap_property P h_closed h_not_le 1
    cases h_total ((m : R) * a) ((m : R) * b + 1) with
    | inl h1 => exact hm_not_le h1
    | inr h1 =>
      have h_rho_le_m := P.rho_monotone h1
      rw [P.rho_add h_total, P.rho_mul h_total, P.rho_mul h_total] at h_rho_le_m
      rw [P.rho_one, P.rho_nat_cast] at h_rho_le_m
      have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
      -- Clear the non-arithmetic hypotheses (negations / the `P.le` relation) so `nlinarith`
      -- (which scans the local context) can't choke on them — some Mathlib builds reject
      -- `¬ P.le …` as "not a comparison". Only real-number facts remain.
      clear h_not_le hm_not_le h1
      nlinarith [h_rho, h_rho_le_m, h_m_pos]
  · exact P.rho_monotone

end StrassenPreorder

/-! ## A spectrum point from a total preorder, and the preorder a point induces -/

namespace AsymptoticSpectrumPoint

variable {R : Type u} [CommSemiring R] {P : StrassenPreorder R}

/-- For a total Strassen preorder, the fractional rank `ρ` is a spectrum point. -/
def ofTotal (Q : StrassenPreorder R) (total : Q.IsTotal) : AsymptoticSpectrumPoint R Q where
  toRingHom := Q.rho_toRingHom total
  monotone' := fun h => Q.rho_monotone h

@[simp] theorem ofTotal_apply (Q : StrassenPreorder R) (total : Q.IsTotal) (a : R) :
    ofTotal Q total a = Q.rho a := rfl

/-- Restrict a spectrum point from a larger preorder `Q` to a smaller `P ≤ Q`. -/
def restrict {P Q : StrassenPreorder R} (h : P ≤ Q) (φ : AsymptoticSpectrumPoint R Q) :
    AsymptoticSpectrumPoint R P where
  toRingHom := φ.toRingHom
  monotone' := fun hab => φ.monotone' (h _ _ hab)

@[simp] theorem restrict_apply {P Q : StrassenPreorder R} (h : P ≤ Q)
    (φ : AsymptoticSpectrumPoint R Q) (a : R) : restrict h φ a = φ a := rfl

/-- The Strassen preorder induced by a spectrum point `φ`: `a ≤ b ↔ φ a ≤ φ b`. -/
def toStrassenPreorder (φ : AsymptoticSpectrumPoint R P) : StrassenPreorder R where
  le a b := φ a ≤ φ b
  le_refl a := le_refl _
  le_trans a b c hab hbc := le_trans hab hbc
  add_right a b hab c := by rw [map_add, map_add]; linarith
  mul_right a b hab c := by
    rw [map_mul, map_mul]
    have h0c : 0 ≤ φ c := by
      rw [← map_zero φ.toRingHom]; exact φ.monotone' (P.zero_le c)
    nlinarith
  zero_le a := φ.monotone' (P.zero_le a)
  nat_order_embedding n m := by rw [map_natCast, map_natCast]; exact Nat.cast_le
  lower_archimedean a := by
    cases P.lower_archimedean a with
    | inl h => left; simp [h]
    | inr h => right; simpa using φ.monotone' h
  upper_archimedean a := by
    obtain ⟨n, h⟩ := P.upper_archimedean a
    exact ⟨n, by simpa using φ.monotone' h⟩

theorem toStrassenPreorder_le_iff (φ : AsymptoticSpectrumPoint R P) (a b : R) :
    φ.toStrassenPreorder.le a b ↔ φ a ≤ φ b := Iff.rfl

theorem toStrassenPreorder_isTotal (φ : AsymptoticSpectrumPoint R P) :
    φ.toStrassenPreorder.IsTotal :=
  fun a b => le_total (φ a) (φ b)

theorem toStrassenPreorder_isClosed (φ : AsymptoticSpectrumPoint R P) :
    φ.toStrassenPreorder.IsClosed := by
  intro a b h
  show φ a ≤ φ b
  obtain ⟨f, hf, hle⟩ := h
  change ∀ n, φ.toStrassenPreorder.le (a ^ n) (↑(f n) * b ^ n) at hle
  have h_phi_le : ∀ n, (φ a) ^ n ≤ f n * (φ b) ^ n := by
    intro n
    have := hle n
    rw [toStrassenPreorder_le_iff] at this
    rw [map_pow, map_mul, map_natCast, map_pow] at this
    exact_mod_cast this
  have h_phi_a_nonneg : 0 ≤ φ a := by
    rw [← map_zero φ.toRingHom]; exact φ.monotone' (P.zero_le a)
  have h_phi_b_nonneg : 0 ≤ φ b := by
    rw [← map_zero φ.toRingHom]; exact φ.monotone' (P.zero_le b)
  by_cases hb : 0 < φ b
  · apply le_of_forall_pos_le_add
    intro δ hδ
    set ε := δ / φ b with hε_def
    have hε : 0 < ε := div_pos hδ hb
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hf ε hε)
    set n := N + 1 with hn_def
    have h_phi_n := h_phi_le n
    have hN' := hN n (Nat.le_add_right N 1)
    have h_pow_pos : 0 < (φ b) ^ n := pow_pos hb n
    have h_ratio : (φ a / φ b) ^ n ≤ (f n : ℝ) := by
      rw [div_pow, div_le_iff₀ h_pow_pos]; exact_mod_cast h_phi_n
    have h_final : (φ a / φ b) ^ n ≤ (1 + ε) ^ n := by
      refine h_ratio.trans ?_
      have : (f n : ℝ) ≤ (1 + ε) ^ (n : ℝ) := hN'
      rw [Real.rpow_natCast] at this; exact this
    have h_base : φ a / φ b ≤ 1 + ε := by
      have h_n_pos : 0 < (n : ℝ) := by positivity
      rw [← Real.rpow_le_rpow_iff (z := (n : ℝ)) (by positivity) (by linarith) h_n_pos]
      simpa only [Real.rpow_natCast] using h_final
    rw [div_le_iff₀ hb] at h_base
    calc φ a ≤ (1 + ε) * φ b := h_base
      _ = φ b + ε * φ b := by ring
      _ = φ b + δ := by rw [hε_def, div_mul_cancel₀ _ (ne_of_gt hb)]
  · have hb0 : φ b = 0 := le_antisymm (not_lt.mp hb) h_phi_b_nonneg
    have := h_phi_le 1
    rw [hb0] at this ⊢
    simpa using this

theorem toStrassenPreorder_le (φ : AsymptoticSpectrumPoint R P) {a b : R} (h : P.le a b) :
    φ.toStrassenPreorder.le a b := φ.monotone' h

/-- For the preorder induced by `φ`, its own fractional rank `ρ` recovers `φ`. -/
theorem rho_of_toStrassenPreorder (φ : AsymptoticSpectrumPoint R P) (a : R) :
    φ.toStrassenPreorder.rho a = φ a := by
  set Q := φ.toStrassenPreorder with hQ
  have h_phi_pos : 0 ≤ φ a := by
    rw [← map_zero φ.toRingHom]; exact φ.monotone' (P.zero_le a)
  apply le_antisymm
  · apply le_of_forall_gt
    intro v hv
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hv
    refine lt_of_le_of_lt ?_ hq2
    apply csInf_le (Q.rho_set_bddBelow a)
    have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt h_phi_pos hq1
    have h_q_num_pos : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq_pos.le)
    set n := q.num.toNat with hn_def
    set m := q.den with hm_def
    have hq_val : (q : ℝ) = (n : ℝ) / (m : ℝ) := by
      rw [Rat.cast_def q]; congr 1; exact_mod_cast (Int.toNat_of_nonneg h_q_num_pos).symm
    refine ⟨n, m, q.pos, ?_, ?_⟩
    · show Q.le ((↑m : R) * a) (↑n : R)
      rw [hQ, toStrassenPreorder_le_iff, map_mul, map_natCast, map_natCast]
      have h_den_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr q.pos
      have hq' : φ a < (n : ℝ) / (m : ℝ) := by rw [← hq_val]; exact hq1
      rw [lt_div_iff₀ h_den_pos] at hq'
      nlinarith
    · exact hq_val
  · apply le_csInf (Q.rho_set_nonempty a)
    rintro x ⟨n, m, hm, h, rfl⟩
    rw [hQ, toStrassenPreorder_le_iff, map_mul, map_natCast, map_natCast] at h
    have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    rw [le_div_iff₀ h_m_pos, mul_comm]; exact h

end AsymptoticSpectrumPoint

/-! ## Spectrum nonemptiness -/

variable {R : Type u} [CommSemiring R]

/-- **Existence of spectrum points.** Every Strassen preorder has at least one
asymptotic-spectrum point, obtained from a maximal (hence total) extension via `ρ`. -/
theorem mme_spectrum_nonempty (P : StrassenPreorder R) :
    Nonempty (AsymptoticSpectrumPoint R P) := by
  obtain ⟨Q, hPQ, hQ_max⟩ := StrassenPreorder.total_extension P
  have hQ_total : Q.IsTotal := hQ_max.IsTotal
  exact ⟨AsymptoticSpectrumPoint.restrict hPQ (AsymptoticSpectrumPoint.ofTotal Q hQ_total)⟩

instance (P : StrassenPreorder R) : Nonempty (AsymptoticSpectrumPoint R P) :=
  mme_spectrum_nonempty P

namespace StrassenPreorder

/-! ## The duality theorem -/

/-- The duality characterization of the asymptotic closure by spectrum points:
`AsymptoticLe P a b` holds iff every spectrum point sends `a` below `b`. -/
theorem asymptoticLe_iff_spectrum_le (P : StrassenPreorder R) (a b : R) :
    AsymptoticLe P a b ↔ ∀ φ : AsymptoticSpectrumPoint R P, φ a ≤ φ b := by
  change (asymptoticClosure P).le a b ↔ _
  rw [asymptoticClosure_eq_intersection_total_closed]
  constructor
  · intro h φ
    have hQ := h φ.toStrassenPreorder (fun x y hxy => φ.toStrassenPreorder_le hxy)
      φ.toStrassenPreorder_isTotal φ.toStrassenPreorder_isClosed
    rwa [AsymptoticSpectrumPoint.toStrassenPreorder_le_iff] at hQ
  · intro h Q hPQ h_total h_closed
    have hφ := h (AsymptoticSpectrumPoint.restrict hPQ
      (AsymptoticSpectrumPoint.ofTotal Q h_total))
    simp only [AsymptoticSpectrumPoint.restrict_apply,
      AsymptoticSpectrumPoint.ofTotal_apply] at hφ
    exact (Q.rho_reflects_le h_total h_closed a b).mp hφ

/-- For a subexponential ℕ-valued sequence `f`, `(f k)^(1/k) ≤ 1 + ε` eventually. -/
private lemma subexp_rpow_eventually_le {f : ℕ → ℕ} (hf : IsSubexponential f)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop, (f k : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε := by
  filter_upwards [hf ε hε, eventually_gt_atTop 0] with k hk hk_pos
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have hfk_nonneg : 0 ≤ (f k : ℝ) := Nat.cast_nonneg _
  have h1e_nonneg : (0 : ℝ) ≤ 1 + ε := by linarith
  have h1k_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc (f k : ℝ) ^ (1 / (k : ℝ))
      ≤ ((1 + ε) ^ (k : ℝ)) ^ (1 / (k : ℝ)) := Real.rpow_le_rpow hfk_nonneg hk h1k_nonneg
    _ = (1 + ε) ^ ((k : ℝ) * (1 / (k : ℝ))) := by rw [← Real.rpow_mul h1e_nonneg]
    _ = (1 + ε) ^ (1 : ℝ) := by rw [mul_one_div_cancel hk_cast_ne]
    _ = 1 + ε := Real.rpow_one _

/-- `asymptoticRank P 0 = 0`. -/
private lemma asymptoticRank_zero (P : StrassenPreorder R) : asymptoticRank P (0 : R) = 0 := by
  have hrank : rank P (0 : R) = 0 := by
    apply Nat.le_zero.mp
    apply rank_le_of_le
    rw [Nat.cast_zero]; exact P.zero_le 0
  unfold asymptoticRank
  have : ∀ n : ℕ, (rank P ((0 : R) ^ (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1)) = 0 := by
    intro n
    rw [zero_pow (Nat.succ_ne_zero n), hrank, Nat.cast_zero]
    rw [Real.zero_rpow]
    positivity
  simp only [this]
  exact ciInf_const

/-- Bridge: if `a` is asymptotically `≤` a natural number `N`, then `asymptoticRank P a ≤ N`. -/
lemma asymptoticRank_le_of_asymptoticLe_natCast (P : StrassenPreorder R)
    {a : R} {N : ℕ} (h : AsymptoticLe P a (N : R)) : asymptoticRank P a ≤ (N : ℝ) := by
  obtain ⟨f, hf, h_le⟩ := h
  have h_rank_bound : ∀ m : ℕ, (rank P (a ^ m) : ℝ) ≤ (f m : ℝ) * (N : ℝ) ^ m := by
    intro m
    have h_cast : P.le (a ^ m) ((f m * N ^ m : ℕ) : R) := by
      have hlm := h_le m
      push_cast at hlm ⊢; convert hlm using 1
    have hrm : rank P (a ^ m) ≤ f m * N ^ m := rank_le_of_le P h_cast
    exact_mod_cast hrm
  by_cases ha : a = 0
  · rw [ha, asymptoticRank_zero]; exact_mod_cast Nat.zero_le N
  have h_lim : Tendsto (fun m : ℕ => (rank P (a ^ m) : ℝ) ^ (1 / (m : ℝ))) atTop
      (𝓝 (asymptoticRank P a)) := tends_to_asymptoticRank P ha
  by_cases hN : N = 0
  · exfalso
    have h1 := h_le 1
    rw [hN] at h1; simp at h1
    have h_rank_le : rank P a ≤ 0 := rank_le_of_le P (by push_cast; exact h1)
    have h_rank_ge : 1 ≤ (rank P (a ^ 1) : ℝ) := rank_pow_ge_one P ha 1
    rw [pow_one] at h_rank_ge
    have : (1 : ℝ) ≤ (0 : ℝ) :=
      h_rank_ge.trans (by exact_mod_cast h_rank_le)
    linarith
  have hN_cast_pos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ := ε / (N : ℝ) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε hN_cast_pos
  have h_eventually : ∀ᶠ m : ℕ in atTop,
      (rank P (a ^ m) : ℝ) ^ (1 / (m : ℝ)) ≤ (1 + δ) * N := by
    filter_upwards [subexp_rpow_eventually_le hf hδ_pos, eventually_gt_atTop 0]
      with m hm_fm hm_pos
    have hm_cast_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hm_inv_nonneg : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    have hfn_nonneg : 0 ≤ (f m : ℝ) := Nat.cast_nonneg _
    have hNm_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ m := by positivity
    have h_rank_nonneg : (0 : ℝ) ≤ rank P (a ^ m) := Nat.cast_nonneg _
    calc (rank P (a ^ m) : ℝ) ^ (1 / (m : ℝ))
        ≤ ((f m : ℝ) * (N : ℝ) ^ m) ^ (1 / (m : ℝ)) :=
          Real.rpow_le_rpow h_rank_nonneg (h_rank_bound m) hm_inv_nonneg
      _ = (f m : ℝ) ^ (1 / (m : ℝ)) * ((N : ℝ) ^ m) ^ (1 / (m : ℝ)) :=
          Real.mul_rpow hfn_nonneg hNm_nonneg
      _ = (f m : ℝ) ^ (1 / (m : ℝ)) * (N : ℝ) := by
          congr 1
          rw [← Real.rpow_natCast (N : ℝ) m, ← Real.rpow_mul (le_of_lt hN_cast_pos),
              mul_one_div_cancel (ne_of_gt hm_cast_pos), Real.rpow_one]
      _ ≤ (1 + δ) * (N : ℝ) := mul_le_mul_of_nonneg_right hm_fm (le_of_lt hN_cast_pos)
  have h_bound : asymptoticRank P a ≤ (1 + δ) * (N : ℝ) := le_of_tendsto h_lim h_eventually
  have h_eq : (1 + δ) * (N : ℝ) = (N : ℝ) + ε := by
    rw [hδ_def, add_mul, one_mul, div_mul_cancel₀]; exact ne_of_gt hN_cast_pos
  linarith [h_bound]

/-- Power law for asymptotic rank (for exponent `≥ 1`). -/
lemma asymptoticRank_pow (P : StrassenPreorder R) (a : R) (k : ℕ) (hk : 1 ≤ k) :
    asymptoticRank P (a ^ k) = (asymptoticRank P a) ^ k := by
  by_cases ha : a = 0
  · have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    have hak : a ^ k = 0 := by rw [ha]; exact zero_pow hk_ne
    rw [hak, asymptoticRank_zero, ha, asymptoticRank_zero, zero_pow hk_ne]
  have hak : a ^ k ≠ 0 := P.pow_ne_zero k ha
  have h_lhs : Tendsto (fun m : ℕ => (rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ))) atTop
      (𝓝 (asymptoticRank P (a ^ k))) := tends_to_asymptoticRank P hak
  have h_rhs_lim : Tendsto (fun n : ℕ => (rank P (a ^ n) : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (asymptoticRank P a)) := tends_to_asymptoticRank P ha
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from hk)
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have h_km_atTop : Tendsto (fun m : ℕ => k * m) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro n
    refine ⟨n, fun m hm => ?_⟩
    calc n = 1 * n := (one_mul n).symm
      _ ≤ k * n := Nat.mul_le_mul_right n hk
      _ ≤ k * m := Nat.mul_le_mul_left k hm
  have h_sub : Tendsto (fun m : ℕ => (rank P (a ^ (k * m)) : ℝ) ^ (1 / ((k * m : ℕ) : ℝ))) atTop
      (𝓝 (asymptoticRank P a)) := h_rhs_lim.comp h_km_atTop
  have h_pow_k : ∀ m : ℕ, 0 < m →
      (rank P (a ^ (k * m)) : ℝ) ^ (1 / ((k * m : ℕ) : ℝ)) =
      ((rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ)) := by
    intro m hm_pos
    have hm_cast_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have h_pow_eq : (a ^ k) ^ m = a ^ (k * m) := by rw [← pow_mul]
    rw [← h_pow_eq]
    have h_rank_nonneg : (0 : ℝ) ≤ rank P ((a ^ k) ^ m) := Nat.cast_nonneg _
    rw [← Real.rpow_mul h_rank_nonneg]
    congr 1
    push_cast; field_simp
  have h_sub' : Tendsto
      (fun m : ℕ => ((rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ)))
      atTop (𝓝 (asymptoticRank P a)) := by
    apply h_sub.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact h_pow_k m hm
  have h_k_pow : Tendsto
      (fun m : ℕ => (((rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ))) ^ k)
      atTop (𝓝 ((asymptoticRank P a) ^ k)) := h_sub'.pow k
  have h_simp : ∀ m : ℕ,
      (((rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ))) ^ k =
      (rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ)) := by
    intro m
    set u : ℝ := (rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ)) with hu_def
    have hu_nonneg : 0 ≤ u := by rw [hu_def]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [← Real.rpow_natCast (u ^ (1 / (k : ℝ))) k, ← Real.rpow_mul hu_nonneg, one_div,
        inv_mul_cancel₀ hk_cast_ne, Real.rpow_one]
  have h_simp' : Tendsto (fun m : ℕ => (rank P ((a ^ k) ^ m) : ℝ) ^ (1 / (m : ℝ)))
      atTop (𝓝 ((asymptoticRank P a) ^ k)) := by
    apply h_k_pow.congr
    intro m; exact h_simp m
  exact tendsto_nhds_unique h_lhs h_simp'

/-- Forward direction: every spectrum-point value is bounded by the asymptotic rank. -/
private lemma spectrum_apply_le_asymptoticRank (P : StrassenPreorder R)
    (φ : AsymptoticSpectrumPoint R P) (a : R) : φ a ≤ asymptoticRank P a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, asymptoticRank_zero]
  have h_phi_nonneg : 0 ≤ φ a := φ.nonneg a
  have h_lim := tends_to_asymptoticRank P ha
  apply ge_of_tendsto h_lim
  filter_upwards [eventually_gt_atTop 0] with k hk_pos
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have h_rank_spec : P.le (a ^ k) ((rank P (a ^ k) : ℕ) : R) := le_rank P (a ^ k)
  have h_phi_monotone : φ (a ^ k) ≤ φ ((rank P (a ^ k) : ℕ) : R) := φ.monotone' h_rank_spec
  rw [map_natCast, map_pow] at h_phi_monotone
  have h_phi_pow_nonneg : 0 ≤ φ a ^ k := pow_nonneg h_phi_nonneg k
  have h_inv_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have h_le_rpow : (φ a ^ k) ^ (1 / (k : ℝ)) ≤ (rank P (a ^ k) : ℝ) ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow h_phi_pow_nonneg h_phi_monotone h_inv_nonneg
  have h_eq : (φ a ^ k) ^ (1 / (k : ℝ)) = φ a := by
    rw [← Real.rpow_natCast (φ a) k, ← Real.rpow_mul h_phi_nonneg,
        mul_one_div_cancel hk_cast_ne, Real.rpow_one]
  linarith [h_le_rpow, h_eq]

/-- For nonzero `a`, the supremum of spectrum-point values is `≥ 1`. -/
private lemma one_le_sup_spectrum (P : StrassenPreorder R) {a : R} (ha : a ≠ 0) :
    (1 : ℝ) ≤ ⨆ φ : AsymptoticSpectrumPoint R P, φ a := by
  have h1a : P.le 1 a := by
    cases P.lower_archimedean a with
    | inl h => exact absurd h ha
    | inr h => exact h
  obtain ⟨φ⟩ := (inferInstance : Nonempty (AsymptoticSpectrumPoint R P))
  have h_mono : φ 1 ≤ φ a := φ.monotone' h1a
  rw [map_one] at h_mono
  exact le_ciSup_of_le (spectrum_eval_bddAbove P a) φ h_mono

/-- The duality theorem, stated inside the `StrassenPreorder` namespace. -/
theorem strassen_duality (P : StrassenPreorder R) (a : R) :
    asymptoticRank P a = ⨆ φ : AsymptoticSpectrumPoint R P, φ a := by
  refine le_antisymm ?_ ?_
  · -- asymptoticRank P a ≤ ⨆ φ, φ a
    by_cases ha : a = 0
    · rw [ha, asymptoticRank_zero]
      obtain ⟨φ⟩ := (inferInstance : Nonempty (AsymptoticSpectrumPoint R P))
      refine le_ciSup_of_le (spectrum_eval_bddAbove P 0) φ ?_
      rw [map_zero]
    set M : ℝ := ⨆ φ : AsymptoticSpectrumPoint R P, φ a with hM_def
    have hM_ge_one : 1 ≤ M := one_le_sup_spectrum P ha
    have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM_ge_one
    have hM_pos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM_ge_one
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have h_asymp_nonneg : 0 ≤ asymptoticRank P a := by
      apply ge_of_tendsto (tends_to_asymptoticRank P ha)
      filter_upwards [eventually_gt_atTop 0] with k _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h_asymp_pow_bound : ∀ k : ℕ, 1 ≤ k →
        (asymptoticRank P a) ^ k ≤ (⌈M ^ k⌉₊ : ℝ) := by
      intro k hk
      have h_all_phi : ∀ φ : AsymptoticSpectrumPoint R P,
          φ (a ^ k) ≤ φ ((⌈M ^ k⌉₊ : ℕ) : R) := by
        intro φ
        rw [map_natCast, map_pow]
        have h_phi_le : φ a ≤ M := le_ciSup (spectrum_eval_bddAbove P a) φ
        have h_phi_nonneg : 0 ≤ φ a := φ.nonneg a
        calc φ a ^ k ≤ M ^ k := pow_le_pow_left₀ h_phi_nonneg h_phi_le k
          _ ≤ (⌈M ^ k⌉₊ : ℝ) := Nat.le_ceil _
      have h_asymp_le : AsymptoticLe P (a ^ k) ((⌈M ^ k⌉₊ : ℕ) : R) :=
        (asymptoticLe_iff_spectrum_le P (a ^ k) ((⌈M ^ k⌉₊ : ℕ) : R)).mpr h_all_phi
      have h_bridge : asymptoticRank P (a ^ k) ≤ (⌈M ^ k⌉₊ : ℝ) :=
        asymptoticRank_le_of_asymptoticLe_natCast P h_asymp_le
      rw [← asymptoticRank_pow P a k hk]
      exact h_bridge
    have hεM_pos : 0 < ε / M := div_pos hε hM_pos
    have h_two_lim : Tendsto (fun k : ℕ => (2 : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
      have hcont : ContinuousAt (fun x : ℝ => (2 : ℝ) ^ x) 0 :=
        Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)
      have h_inv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h := hcont.tendsto.comp h_inv
      simpa only [Real.rpow_zero] using h
    have h_eventually : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε / M := by
      have : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (1 / (k : ℝ)) ∈ Set.Iio (1 + ε / M) :=
        h_two_lim.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [this] with k hk
      exact le_of_lt hk
    obtain ⟨k, hk, hk_bound⟩ : ∃ k : ℕ, 1 ≤ k ∧ (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε / M := by
      obtain ⟨k, hk⟩ := (h_eventually.and (eventually_ge_atTop 1)).exists
      exact ⟨k, hk.2, hk.1⟩
    have h_asymp_k_bound : (asymptoticRank P a) ^ k ≤ (⌈M ^ k⌉₊ : ℝ) := h_asymp_pow_bound k hk
    have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from hk)
    have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
    have h_inv_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h_asymp_pow_nonneg : 0 ≤ (asymptoticRank P a) ^ k := pow_nonneg h_asymp_nonneg k
    have h_rpow_le : ((asymptoticRank P a) ^ k) ^ (1 / (k : ℝ)) ≤ (⌈M ^ k⌉₊ : ℝ) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow h_asymp_pow_nonneg h_asymp_k_bound h_inv_nonneg
    have h_lhs_eq : ((asymptoticRank P a) ^ k) ^ (1 / (k : ℝ)) = asymptoticRank P a := by
      rw [← Real.rpow_natCast (asymptoticRank P a) k, ← Real.rpow_mul h_asymp_nonneg,
          mul_one_div_cancel hk_cast_ne, Real.rpow_one]
    have hMk_pos : 0 < M ^ k := pow_pos hM_pos k
    have hMk_nonneg : 0 ≤ M ^ k := le_of_lt hMk_pos
    have h_ceil_bound : (⌈M ^ k⌉₊ : ℝ) ≤ 2 * M ^ k := by
      have h1 : (⌈M ^ k⌉₊ : ℝ) ≤ M ^ k + 1 := by
        have := Nat.ceil_lt_add_one (le_of_lt hMk_pos); linarith
      have hMk_ge_one : 1 ≤ M ^ k := one_le_pow₀ hM_ge_one
      linarith
    have h_ceil_nonneg : (0 : ℝ) ≤ (⌈M ^ k⌉₊ : ℝ) := Nat.cast_nonneg _
    have h_ceil_rpow_le : (⌈M ^ k⌉₊ : ℝ) ^ (1 / (k : ℝ)) ≤ (2 * M ^ k) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow h_ceil_nonneg h_ceil_bound h_inv_nonneg
    have h_2Mk_rpow : (2 * M ^ k) ^ (1 / (k : ℝ)) = (2 : ℝ) ^ (1 / (k : ℝ)) * M := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMk_nonneg]
      congr 1
      rw [← Real.rpow_natCast M k, ← Real.rpow_mul hM_nonneg,
          mul_one_div_cancel hk_cast_ne, Real.rpow_one]
    have h_prod_le : (2 : ℝ) ^ (1 / (k : ℝ)) * M ≤ (1 + ε / M) * M :=
      mul_le_mul_of_nonneg_right hk_bound hM_nonneg
    have h_arith : (1 + ε / M) * M = M + ε := by field_simp
    linarith [h_rpow_le, h_lhs_eq, h_ceil_rpow_le, h_2Mk_rpow, h_prod_le, h_arith]
  · -- ⨆ φ, φ a ≤ asymptoticRank P a
    apply ciSup_le
    intro φ
    exact spectrum_apply_le_asymptoticRank P φ a

end StrassenPreorder

/-- **Strassen's duality theorem.** The asymptotic rank equals the supremum of the
spectrum-point evaluations: `asymptoticRank P a = ⨆ φ, φ a`. -/
theorem mme_strassen_duality {R : Type u} [CommSemiring R] (P : StrassenPreorder R) (a : R) :
    StrassenPreorder.asymptoticRank P a = ⨆ φ : AsymptoticSpectrumPoint R P, φ a :=
  P.strassen_duality a

/-- Each spectrum-point evaluation underestimates the asymptotic rank:
`φ a ≤ asymptoticRank P a`. Immediate from duality + `spectrum_eval_bddAbove`. -/
theorem StrassenPreorder.eval_le_asymptoticRank {R : Type u} [CommSemiring R]
    (P : StrassenPreorder R) (a : R) (φ : AsymptoticSpectrumPoint R P) :
    φ a ≤ StrassenPreorder.asymptoticRank P a := by
  rw [mme_strassen_duality P a]
  exact le_ciSup (StrassenPreorder.spectrum_eval_bddAbove P a) φ

end MME


