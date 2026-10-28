-- Prove2me | solution 1 for zeta_ne_zero_of_mem_strip_of_abs_im_le_fourteen
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:11:30.389682+00:00
-- url     : https://prove2.me/submissions/e9737340-dcaf-44a7-a8d3-c8d8f34f5262

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_six
import Theorems.Thm_riemannZeta_conj

/-!
# Zero-free rectangle `0 < Re s < 1`, `|Im s| ≤ 14` for the Riemann zeta function

Self-contained port to the Mathlib `777aaa6` environment of three existing `0df444a` platform
results (all Apache-2.0 platform contributions; ported with fixes for the older Mathlib):

* the first-order Euler–Maclaurin machinery for `ζ` from the definitions bundle `SWPort_000`
  (itself a port of PrimeNumberTheoremAnd, Apache 2.0), trimmed to what is needed;
* `ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one` (accepted proof by Nickrobbins95);
* the kernel-checked quadtree certificate for `6 ≤ Im s ≤ 14` from the accepted proof of
  `TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen` (by Nickrobbins95).

`|Im s| ≤ 6` is the Proved platform theorem `zeta_ne_zero_of_mem_strip_of_abs_im_le_six`;
negative ordinates use the Proved platform theorem `riemannZeta_conj`.
-/

section
-- module Solutions.Artin.SW.Def.Zeta23_FromPNTPlus_EulerMaclaurin
namespace SWPort.Z
/-! Ported from prove2.me definition bundle `Zeta23_FromPNTPlus_EulerMaclaurin` (9a4fbc6e-6e67-437e-a93a-d98b6d9dc79f, by Community (Bot)). -/

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

@[expose] public section

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
end

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Def.Zeta23_FromPNTPlus_ResidueCalcOnRectangles
namespace SWPort.Z
/-! Ported from prove2.me definition bundle `Zeta23_FromPNTPlus_ResidueCalcOnRectangles` (fe5719ab-96b8-4989-9ccc-b7e429ace1c2, by Community (Bot)). -/











/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}





/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s




































/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/








-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.





-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.



-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Def.Zeta23_FromPNTPlus_ZetaBounds
namespace SWPort.Z
/-! Ported from prove2.me definition bundle `Zeta23_FromPNTPlus_ZetaBounds` (1089e2e9-050b-4f9b-b2fd-f593ab723dc8, by Community (Bot)). -/

































/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics






local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta





-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/




-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/








noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`







































noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))





-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`





































































-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**



/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**



-- **End collaboration**





open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort.Z
end


section
-- module Solutions.Artin.SW.Thm.Zeta23_hasDerivAt_Zeta0Integral
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23_hasDerivAt_Zeta0Integral` (53b7dc4c-4919-4eb2-9666-a110621030cc, statement by Community (Bot)); proof = accepted direct submission 96e5335d-a890-4d74-9dd8-3b5d1ec73ee5 by Community (Bot). -/


































-- from Zeta23.FromPNTPlus.ZetaBounds
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics






local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta





-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/




-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/









/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`












lemma ZetaSum_aux1_3_p2 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
















lemma ZetaSum_aux2a_p2 : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3_p2


lemma integrableOn_of_Zeta0_fun_p2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a_p2
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor






open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a_p2
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp







-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`





































































-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**



/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**



-- **End collaboration**





open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients


set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
open MeasureTheory

theorem _root_.SWPort.Z.Zeta23_hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert integrableOn_of_Zeta0_fun_p2 Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert integrableOn_of_Zeta0_fun_p2 Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3_p2 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_isPathConnected_aux
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23_isPathConnected_aux` (cd890556-ebf6-4ed6-aba8-eb27d19508ff, statement by Community (Bot)); proof = accepted direct submission c89b881b-bc15-49ea-bc6f-e2d9008752e3 by Community (Bot). -/


































-- from Zeta23.FromPNTPlus.ZetaBounds
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics






local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta





-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/




-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/









/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`












































-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`





































































-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**



/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**



-- **End collaboration**





open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients


set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics

theorem _root_.SWPort.Z.Zeta23_isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_Zeta0EqZeta
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23_Zeta0EqZeta` (91926c43-6503-4817-bea5-55f335881cb0, statement by Community (Bot)); proof = accepted sketch submission fad1cbf6-831c-4515-aaca-6e6d03432b4f by Community (Bot). -/




































-- from Zeta23.FromPNTPlus.Auxiliary
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Auxiliary.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header (upstream has no blueprint annotations
or intra-project imports in this file).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

/-!
### Auxiliary lemmas
-/


lemma _root_.DifferentiableAt.comp_ofReal_p1 {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt








end

-- from Zeta23.FromPNTPlus.EulerMaclaurin
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/


/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

@[expose] public section

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1 <;> try with_reducible_and_instances rfl
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end
end

-- from Zeta23.FromPNTPlus.ZetaBounds
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]





local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta





-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/




-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/









/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma _root_.Real.differentiableAt_cpow_const_of_ne_p1 (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal_p1 (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma _root_.Complex.one_div_cpow_eq_p1 {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1 <;> try with_reducible_and_instances rfl
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    rw [sub_neg_eq_add]; simp only [Algebra.cast, Complex.coe_algebraMap]; show (∫ x in a..b, φ x) + ((⌊b⌋₊:ℂ) + 1/2 - (b:ℂ)) * φ b - ((⌊a⌋₊:ℂ) + 1/2 - (a:ℂ)) * φ a + (∫ t in a..b, deriv φ t * ((t:ℂ) - (⌊t⌋₊:ℂ) - 1/2)) = (φ a * ((a:ℂ) - (⌊a⌋₊:ℂ) - 1/2) - φ b * ((b:ℂ) - (⌊b⌋₊:ℂ) - 1/2) + ∫ x in a..b, φ x) + ∫ t in a..b, deriv φ t * ((t:ℂ) - (⌊t⌋₊:ℂ) - 1/2); ring
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1 <;> try with_reducible_and_instances rfl
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq_p1 ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne_p1 s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert this using 2 <;> try with_reducible_and_instances rfl
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

set_option backward.isDefEq.respectTransparency false in
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1 <;> try with_reducible_and_instances rfl
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf




lemma ZetaSum_aux1_3_p0 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩










lemma _root_.Finset.Ioc_eq_Ico_p1 (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega



lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma _root_.Complex.cpow_tendsto_p1 {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma _root_.Complex.cpow_inv_tendsto_p1 {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a_p0 : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3_p0

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico_p1]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1 <;> try with_reducible_and_instances rfl
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun_p0 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a_p0
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto_p1 s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto_p1 (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun_p0 N_pos <| by positivity) tendsto_natCast_atTop_atTop




lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)





lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1 <;> try with_reducible_and_instances rfl
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1 <;> try with_reducible_and_instances rfl
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1 <;> try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1 <;> try with_reducible_and_instances rfl
    all_goals (ring_nf; simp [cpow_neg])
  · convert HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1 <;> try with_reducible_and_instances rfl
    · ring
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert hasDerivAt_id s |>.mul <| Zeta23_hasDerivAt_Zeta0Integral Npos reS_pos using 1 <;> try with_reducible_and_instances rfl

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt





































































-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**



/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**



-- **End collaboration**





open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients


set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics

theorem _root_.SWPort.Z.Zeta23_Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr Zeta23_isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

end SWPort.Z
end

section
namespace SWPort.Z
open Set
lemma ZetaSum_aux1_3_p1 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma ZetaSum_aux2a_p1 : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3_p1


lemma integrableOn_of_Zeta0_fun_p1 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a_p1
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
end SWPort.Z
end


/-!
# Euler–Maclaurin for ζ(s) with ν = 1 (EM3 child of ac5b0112)

Route: `SWPort.Z.Zeta23_Zeta0EqZeta` (platform definition bundle `Def_SWPort_000`) gives the first-order
Euler–Maclaurin form `ζ(s) = Σ_{n ≤ N} n^{-s} - N^{1-s}/(1-s) - N^{-s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 - x) x^{-s-1} dx`
for `0 < Re s`, `s ≠ 1`. With `P_k(x) = B_k({x})` (right derivative `k P_{k-1}`, continuous for `k ≥ 2`),
the function `F(x) = P_2(x)/2 · x^{-(s+1)} + (s+1)/6 · P_3(x) x^{-s-2}` has right derivative
`P_1(x) x^{-(s+1)} - (s+1)(s+2)/6 · P_3(x) x^{-s-3}` at every `x > 0`; FTC on `[N, M]` (natural `M`, where
`F(M) = M^{-(s+1)}/12`) and `M → ∞` give the remainder integral in the `B_3` form.
-/

set_option autoImplicit false

namespace ZetaEM3Aux

theorem _root_.HasDerivWithinAt.ofReal_comp {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ}
    (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => (f y : ℂ)) (f' : ℂ) s x := by
  simpa using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt x h)

open Complex MeasureTheory Set Filter Topology

/-- Right derivative of `x ↦ B_k({x})`. -/
theorem hasDerivWithinAt_bernoulliFun_fract (k : ℕ) (x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => bernoulliFun k (Int.fract y))
      ((k : ℝ) * bernoulliFun (k - 1) (Int.fract x)) (Ici x) x := by
  have h1 : HasDerivAt (fun y : ℝ => bernoulliFun k (y - ((⌊x⌋ : ℤ) : ℝ)))
      ((k : ℝ) * bernoulliFun (k - 1) (Int.fract x)) x := by
    exact HasDerivAt.comp_sub_const x ((⌊x⌋ : ℤ) : ℝ)
      (hasDerivAt_bernoulliFun k (x - ((⌊x⌋ : ℤ) : ℝ)))
  have h2 : (fun y : ℝ => bernoulliFun k (Int.fract y)) =ᶠ[𝓝[≥] x]
      (fun y : ℝ => bernoulliFun k (y - ((⌊x⌋ : ℤ) : ℝ))) := by
    filter_upwards [Ico_mem_nhdsGE (Int.lt_floor_add_one x)] with y hy
    have hfl : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]
      exact ⟨(Int.floor_le x).trans hy.1, hy.2⟩
    show bernoulliFun k (y - ((⌊y⌋ : ℤ) : ℝ)) = _
    rw [hfl]
  exact h1.hasDerivWithinAt.congr_of_eventuallyEq h2 rfl

/-- `x ↦ B_k({x})` is continuous for `k ≠ 1`. -/
theorem continuous_bernoulliFun_fract {k : ℕ} (hk : k ≠ 1) :
    Continuous (fun y : ℝ => bernoulliFun k (Int.fract y)) :=
  (continuous_bernoulliFun k).continuousOn.comp_fract'' (bernoulliFun_endpoints_eq_of_ne_one hk).symm

theorem exists_bound_bernoulliFun_fract (k : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ, ‖bernoulliFun k (Int.fract y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  exact ⟨C, fun y => hC _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩⟩

theorem integrableOn_B3 {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)) (Ioi a) := by
  obtain ⟨C, hC⟩ := exists_bound_bernoulliFun_fract 3
  refine Integrable.bdd_mul (c := C) ?_ ?_ ?_
  · refine integrableOn_Ioi_cpow_of_lt ?_ ha
    simp only [sub_re, neg_re, re_ofNat]
    linarith
  · exact (continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 3) (by norm_num))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by simpa only [Complex.norm_real] using hC x)

/-- The antiderivative. -/
theorem hasDerivWithinAt_F {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt
      (fun y : ℝ => (bernoulliFun 2 (Int.fract y) : ℂ) / 2 * (y : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract y) : ℂ) * (y : ℂ) ^ (-s - 2)))
      (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      (Ici x) x := by
  have hr1 : -(s + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [neg_re, add_re, one_re, zero_re] at this
    linarith
  have hr2 : -s - 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, neg_re, re_ofNat, zero_re] at this
    linarith
  have hB2 := (hasDerivWithinAt_bernoulliFun_fract 2 x).ofReal_comp
  have hB3 := (hasDerivWithinAt_bernoulliFun_fract 3 x).ofReal_comp
  have hP1 := (hasDerivAt_ofReal_cpow_const hx.ne' hr1).hasDerivWithinAt (s := Ici x)
  have hP2 := (hasDerivAt_ofReal_cpow_const hx.ne' hr2).hasDerivWithinAt (s := Ici x)
  have hF := ((hB2.div_const 2).mul hP1).add ((hB3.mul hP2).const_mul ((s + 1) / 6))
  refine hF.congr_deriv ?_
  have e1 : -(s + 1) - 1 = -s - 2 := by ring
  have e2 : -s - 2 - 1 = -s - 3 := by ring
  rw [e1, e2]
  norm_num [bernoulliFun_one]
  rw [show Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) from rfl]
  push_cast
  ring

/-- Continuity of the antiderivative on `[a, b]`, `0 < a`. -/
theorem continuousOn_F {s : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun y : ℝ => (bernoulliFun 2 (Int.fract y) : ℂ) / 2 * (y : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract y) : ℂ) * (y : ℂ) ^ (-s - 2))) (Icc a b) := by
  have hc2 := continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 2) (by norm_num))
  have hc3 := continuous_ofReal.comp (continuous_bernoulliFun_fract (k := 3) (by norm_num))
  have hp : ∀ c : ℂ, ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Icc a b) := fun c y hy =>
    (continuousAt_ofReal_cpow_const y c (Or.inr (ha.trans_le hy.1).ne')).continuousWithinAt
  exact ((hc2.continuousOn.div_const 2).mul (hp _)).add
    (continuousOn_const.mul (hc3.continuousOn.mul (hp _)))

/-- The integrand `g`: the first-order remainder integrand (negated) minus the `B_3` remainder. -/
theorem integrableOn_g {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => -(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      (Ioi (N : ℝ)) := by
  have h1 := SWPort.Z.integrableOn_of_Zeta0_fun_p1 hN hs
  have h3 := integrableOn_B3 (a := (N : ℝ)) (by exact_mod_cast hN) hs
  have := h1.neg.sub (h3.const_mul ((s + 1) * (s + 2) / 6))
  refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.neg_apply, Pi.sub_apply, neg_mul]

/-- Value of the antiderivative at a natural number. -/
theorem F_nat {s : ℂ} (n : ℕ) :
    (bernoulliFun 2 (Int.fract (n : ℝ)) : ℂ) / 2 * ((n : ℝ) : ℂ) ^ (-(s + 1))
        + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract (n : ℝ)) : ℂ) * ((n : ℝ) : ℂ) ^ (-s - 2))
      = (n : ℂ) ^ (-(s + 1)) / 12 := by
  have h3 : bernoulliFun 3 0 = 0 := by
    rw [bernoulliFun_eval_zero, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]
    simp
  have h2 : bernoulliFun 2 0 = 1 / 6 := by
    rw [bernoulliFun_two]; norm_num
  rw [Int.fract_natCast, h2, h3, Complex.ofReal_natCast]
  push_cast
  ring

/-- FTC on `[N, b]`. -/
theorem integral_g_interval {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) {b : ℝ} (hb : (N : ℝ) ≤ b) :
    ∫ x in (N : ℝ)..b, (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      = ((bernoulliFun 2 (Int.fract b) : ℂ) / 2 * (b : ℂ) ^ (-(s + 1))
          + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract b) : ℂ) * (b : ℂ) ^ (-s - 2)))
        - ((bernoulliFun 2 (Int.fract (N : ℝ)) : ℂ) / 2 * ((N : ℝ) : ℂ) ^ (-(s + 1))
          + (s + 1) / 6 * ((bernoulliFun 3 (Int.fract (N : ℝ)) : ℂ) * ((N : ℝ) : ℂ) ^ (-s - 2))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb (continuousOn_F hN') ?_ ?_
  · intro x hx
    exact (hasDerivWithinAt_F hs (hN'.trans hx.1)).mono Ioi_subset_Ici_self
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact (integrableOn_g hN hs).mono_set Ioc_subset_Ioi_self

/-- The improper integral of `g` over `(N, ∞)`. -/
theorem integral_Ioi_g {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi (N : ℝ), (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)))
      = -((N : ℂ) ^ (-(s + 1)) / 12) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi (N : ℝ) (integrableOn_g hN hs)
    tendsto_natCast_atTop_atTop
  have hs1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have hlim : Tendsto (fun M : ℕ => (M : ℂ) ^ (-(s + 1)) / 12 - (N : ℂ) ^ (-(s + 1)) / 12) atTop
      (𝓝 (0 / 12 - (N : ℂ) ^ (-(s + 1)) / 12)) := by
    refine (Tendsto.div_const ?_ 12).sub_const _
    simp_rw [Complex.cpow_neg]
    exact Complex.cpow_inv_tendsto_p1 hs1
  have h2 : Tendsto (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ),
      (-(((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
        - (s + 1) * (s + 2) / 6 * ((bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3))))
      atTop (𝓝 (0 / 12 - (N : ℂ) ^ (-(s + 1)) / 12)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    rw [integral_g_interval hN hs (by exact_mod_cast hM), F_nat, F_nat]
  rw [tendsto_nhds_unique h1 h2]
  ring

/-- The remainder integral of `ζ₀` in third-order form. -/
theorem integral_Ioi_floor_eq {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioi (N : ℝ), (((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1))
      = (N : ℂ) ^ (-(s + 1)) / 12
        - (s + 1) * (s + 2) / 6 *
          ∫ x in Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have h := integral_Ioi_g hN hs
  have hi1 := SWPort.Z.integrableOn_of_Zeta0_fun_p1 hN hs
  have hi3 := integrableOn_B3 (a := (N : ℝ)) (by exact_mod_cast hN) hs
  rw [integral_sub (IntegrableOn.congr_fun hi1.neg (fun x _ => by simp only [Pi.neg_apply, neg_mul])
      measurableSet_Ioi) (hi3.const_mul _)] at h
  simp only [neg_mul, integral_neg, integral_const_mul] at h
  have e := MeasureTheory.integral_const_mul (μ := volume.restrict (Ioi (N:ℝ))) ((s + 1) * (s + 2) / 6)
    (fun a : ℝ => (bernoulliFun 3 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s - 3))
  erw [e] at h
  have h' : -(∫ x in Ioi (N : ℝ), (((⌊x⌋ : ℤ) : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-(s + 1)))
      - (s + 1) * (s + 2) / 6 * ∫ x in Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)
      = -((N : ℂ) ^ (-(s + 1)) / 12) := h
  linear_combination -h'

theorem sum_range_eq_sum_Icc (N : ℕ) {s : ℂ} (hs : s ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp only [Nat.cast_zero, Complex.zero_cpow hs, div_zero, zero_add]
  rw [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [one_div, Complex.cpow_neg]

end ZetaEM3Aux

theorem ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s)
      - (N : ℂ) ^ (-s) / 2 + s * (N : ℂ) ^ (-s - 1) / 12
      - s * (s + 1) * (s + 2) / 6 *
          ∫ x in Set.Ioi (N : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have hN0 : 0 < N := hN
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [← SWPort.Z.Zeta23_Zeta0EqZeta hN0 hs hs1, SWPort.Z.riemannZeta0_apply,
    ZetaEM3Aux.integral_Ioi_floor_eq hN0 hs, ZetaEM3Aux.sum_range_eq_sum_Icc N hs0]
  have e : -(s + 1) = -s - 1 := by ring
  rw [e]
  ring




set_option autoImplicit false
set_option linter.all false

/-!
# ac5b0112: ζ(s) ≠ 0 for 0 < Re s < 1, 2 ≤ Im s ≤ 14 (generated by `sim/emit_frame.py full`)

`theorem solution` (end of file) splits at Im s = 6: `2 ≤ Im s ≤ 6` is the Proved platform theorem
d1d6b916 (`ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six`, via `abs_le`), and
`6 ≤ Im s ≤ 14` is `ZFrame.zeta_ne_zero_6_14`: eight unit strips, 638 kernel-checked quadtree
leaves, each box proved zero-free by `qtOK_sound` from the EM3 identity child.

## The frame

Stage S1 (`ZFrame_slice.lean`: offset Nat balls, `cmul/cadd/csub/cdivn/rmul`, Horner `cexp`, `sqn`) plus
stage S2 (`frame/src/s2_*.lean.part`): `epow`, exact-rational log certificates, the Dirichlet sum,
`em3_bound` from the EM3 identity child, the box theorem `boxN_sound` and the quadtree theorem
`qtOK_sound`.  Rules (S1 module doc): never simp-unfold an op, rewrite with its `_eq` lemma.
`linter.all false` only silences linters; it does not change what is checked.
-/

namespace ZFrame

structure NB where
  a : Nat
  b : Nat
  r : Nat
  v : Bool

/-! ## Kernel-side definitions (the probe text, so the measured kernel speed applies) -/

def up (x d : Nat) : Nat := Nat.add (Nat.div x d) 1
def dist (v : Nat) : Nat := Nat.add (Nat.sub v 72057594037927936) (Nat.sub 72057594037927936 v)

def cmul (x y : NB) : NB :=
  match Nat.add (Nat.add (Nat.mul x.a y.a) (Nat.mul 72057594037927936 (Nat.add x.b y.b))) 20282409603651670423947251286016,
        Nat.add (Nat.mul x.b y.b) (Nat.mul 72057594037927936 (Nat.add x.a y.a)),
        Nat.add (Nat.add (Nat.mul x.a y.b) (Nat.mul x.b y.a)) 10404876126673306927484939909726208,
        Nat.mul 72057594037927936 (Nat.add (Nat.add x.a x.b) (Nat.add y.a y.b)) with
  | hre, lre, him, lim =>
  ⟨Nat.div (Nat.sub hre lre) 281474976710656, Nat.div (Nat.sub him lim) 281474976710656,
   Nat.add (up (Nat.add (Nat.add (Nat.mul (Nat.add (dist x.a) (dist x.b)) y.r)
     (Nat.mul (Nat.add (dist y.a) (dist y.b)) x.r)) (Nat.mul 2 (Nat.mul x.r y.r))) 281474976710656) 1,
   x.v && y.v && Nat.ble lre hre && Nat.ble lim him⟩

def cadd (x y : NB) : NB :=
  match Nat.add x.a y.a, Nat.add x.b y.b with
  | sa, sb => ⟨Nat.sub sa 72057594037927936, Nat.sub sb 72057594037927936, Nat.add x.r y.r, x.v && y.v && Nat.ble 72057594037927936 sa && Nat.ble 72057594037927936 sb⟩
def csub (x y : NB) : NB :=
  match Nat.add x.a 72057594037927936, Nat.add x.b 72057594037927936 with
  | sa, sb => ⟨Nat.sub sa y.a, Nat.sub sb y.b, Nat.add x.r y.r, x.v && y.v && Nat.ble y.a sa && Nat.ble y.b sb⟩
def cdivn (x : NB) (j : Nat) : NB :=
  ⟨Nat.div (Nat.add x.a (Nat.mul (Nat.sub j 1) 72057594037927936)) j, Nat.div (Nat.add x.b (Nat.mul (Nat.sub j 1) 72057594037927936)) j,
   Nat.add (Nat.div (Nat.add x.r (Nat.sub j 1)) j) 1, x.v⟩
def one : NB := ⟨72339069014638592, 72057594037927936, 0, true⟩

/-- one Horner step: `1 + z·acc/(j+1)` -/
def hstep (z : NB) (j : Nat) (acc : NB) : NB := cadd one (cdivn (cmul z acc) (j + 1))
def horner (z : NB) : Nat → NB → NB
  | 0 => fun acc => acc
  | j + 1 => fun acc => horner z j (hstep z j acc)

def ubz (z : NB) : Nat := Nat.add (Nat.add (dist z.a) (dist z.b)) (Nat.mul 2 z.r)
/-- `Complex.exp_bound` with n = 16, in ulps: `≥ 2^48 · (u/2^48)^16 · 17 / (16! · 16)` -/
def remb (u : Nat) : Nat :=
  up (Nat.mul (Nat.add (Nat.shiftRight (Nat.pow u 16) 720) 1) 17) 334764638208000
def cexp (z : NB) : NB :=
  match horner z 15 one with
  | ⟨a, b, r, v⟩ => ⟨a, b, Nat.add r (remb (ubz z)), v⟩
def sqn : Nat → NB → NB
  | 0 => fun x => x
  | k + 1 => fun x => sqn k (cmul x x)

/-- `(log n) · ball`, given `|log n − L/2^48| ≤ 2^-48` -/
def rmul (L : Nat) (w : NB) : NB :=
  match Nat.add (Nat.mul L w.a) 20282409603651670423947251286016, Nat.add (Nat.mul L w.b) 20282409603651670423947251286016, Nat.mul L 72057594037927936 with
  | ha, hb, lo =>
  ⟨Nat.div (Nat.sub ha lo) 281474976710656, Nat.div (Nat.sub hb lo) 281474976710656,
   Nat.add (up (Nat.add (Nat.add (Nat.add (Nat.mul L w.r) (dist w.a)) (dist w.b)) w.r) 281474976710656) 1,
   w.v && Nat.ble lo ha && Nat.ble lo hb⟩

/-! ## Structure equations (the only way the proofs below open an op; see the module doc) -/

theorem cmul_eq (x y : NB) : cmul x y =
    ⟨Nat.div (Nat.sub (Nat.add (Nat.add (Nat.mul x.a y.a) (Nat.mul 72057594037927936 (Nat.add x.b y.b))) 20282409603651670423947251286016)
        (Nat.add (Nat.mul x.b y.b) (Nat.mul 72057594037927936 (Nat.add x.a y.a)))) 281474976710656,
     Nat.div (Nat.sub (Nat.add (Nat.add (Nat.mul x.a y.b) (Nat.mul x.b y.a)) 10404876126673306927484939909726208)
        (Nat.mul 72057594037927936 (Nat.add (Nat.add x.a x.b) (Nat.add y.a y.b)))) 281474976710656,
     Nat.add (up (Nat.add (Nat.add (Nat.mul (Nat.add (dist x.a) (dist x.b)) y.r)
       (Nat.mul (Nat.add (dist y.a) (dist y.b)) x.r)) (Nat.mul 2 (Nat.mul x.r y.r))) 281474976710656) 1,
     x.v && y.v &&
       Nat.ble (Nat.add (Nat.mul x.b y.b) (Nat.mul 72057594037927936 (Nat.add x.a y.a)))
         (Nat.add (Nat.add (Nat.mul x.a y.a) (Nat.mul 72057594037927936 (Nat.add x.b y.b))) 20282409603651670423947251286016) &&
       Nat.ble (Nat.mul 72057594037927936 (Nat.add (Nat.add x.a x.b) (Nat.add y.a y.b)))
         (Nat.add (Nat.add (Nat.mul x.a y.b) (Nat.mul x.b y.a)) 10404876126673306927484939909726208)⟩ := rfl

theorem cadd_eq (x y : NB) : cadd x y =
    ⟨Nat.sub (Nat.add x.a y.a) 72057594037927936, Nat.sub (Nat.add x.b y.b) 72057594037927936,
     Nat.add x.r y.r,
     x.v && y.v && Nat.ble 72057594037927936 (Nat.add x.a y.a) &&
       Nat.ble 72057594037927936 (Nat.add x.b y.b)⟩ := rfl

theorem csub_eq (x y : NB) : csub x y =
    ⟨Nat.sub (Nat.add x.a 72057594037927936) y.a, Nat.sub (Nat.add x.b 72057594037927936) y.b,
     Nat.add x.r y.r,
     x.v && y.v && Nat.ble y.a (Nat.add x.a 72057594037927936) &&
       Nat.ble y.b (Nat.add x.b 72057594037927936)⟩ := rfl

theorem cdivn_eq (x : NB) (j : Nat) : cdivn x j =
    ⟨Nat.div (Nat.add x.a (Nat.mul (Nat.sub j 1) 72057594037927936)) j,
     Nat.div (Nat.add x.b (Nat.mul (Nat.sub j 1) 72057594037927936)) j,
     Nat.add (Nat.div (Nat.add x.r (Nat.sub j 1)) j) 1, x.v⟩ := rfl

theorem rmul_eq (L : Nat) (w : NB) : rmul L w =
    ⟨Nat.div (Nat.sub (Nat.add (Nat.mul L w.a) 20282409603651670423947251286016) (Nat.mul L 72057594037927936)) 281474976710656,
     Nat.div (Nat.sub (Nat.add (Nat.mul L w.b) 20282409603651670423947251286016) (Nat.mul L 72057594037927936)) 281474976710656,
     Nat.add (up (Nat.add (Nat.add (Nat.add (Nat.mul L w.r) (dist w.a)) (dist w.b)) w.r) 281474976710656) 1,
     w.v && Nat.ble (Nat.mul L 72057594037927936) (Nat.add (Nat.mul L w.a) 20282409603651670423947251286016) &&
       Nat.ble (Nat.mul L 72057594037927936) (Nat.add (Nat.mul L w.b) 20282409603651670423947251286016)⟩ := rfl

theorem hstep_eq (z : NB) (j : Nat) (acc : NB) :
    hstep z j acc = cadd one (cdivn (cmul z acc) (j + 1)) := rfl

theorem horner_zero (z acc : NB) : horner z 0 acc = acc := rfl

theorem horner_succ (z : NB) (j : Nat) :
    horner z (j + 1) = fun acc => horner z j (hstep z j acc) := by
  rw [horner]

theorem horner_succ' (z acc : NB) (j : Nat) : horner z (j + 1) acc = horner z j (hstep z j acc) :=
  congrFun (horner_succ z j) acc

theorem sqn_zero (x : NB) : sqn 0 x = x := rfl

theorem sqn_succ (k : Nat) : sqn (k + 1) = fun x => sqn k (cmul x x) := by
  rw [sqn]

theorem sqn_succ' (k : Nat) (x : NB) : sqn (k + 1) x = sqn k (cmul x x) :=
  congrFun (sqn_succ k) x

theorem cexp_eq (z : NB) (a b r : Nat) (v : Bool) (hH : horner z 15 one = ⟨a, b, r, v⟩) :
    cexp z = ⟨a, b, Nat.add r (remb (ubz z)), v⟩ := by
  unfold cexp
  rw [hH]

/-! ## Semantics -/

/-- `x` encloses `z`: both coordinates of `z`, scaled by `2^48`, lie within `x.r` of the offset centre. -/
def NB.Mem (x : NB) (z : ℂ) : Prop :=
  |281474976710656 * z.re - ((x.a : ℝ) - 72057594037927936)| ≤ x.r ∧
  |281474976710656 * z.im - ((x.b : ℝ) - 72057594037927936)| ≤ x.r

theorem ndiv_eq (x y : ℕ) : Nat.div x y = x / y := rfl
theorem npow_eq (x y : ℕ) : Nat.pow x y = x ^ y := rfl
theorem nshr_eq (x y : ℕ) : Nat.shiftRight x y = x >>> y := rfl

/-- Nat floor division, read in `ℝ`: `q·j ≤ n` and `n + 1 ≤ q·j + j`. -/
theorem div_bounds (n j : ℕ) (hj : 0 < j) :
    ((n / j : ℕ) : ℝ) * j ≤ n ∧ (n : ℝ) + 1 ≤ ((n / j : ℕ) : ℝ) * j + j := by
  have h1 : n / j * j ≤ n := Nat.div_mul_le_self n j
  have h2 : n + 1 ≤ n / j * j + j := Nat.lt_div_mul_add hj
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- `up x d = ⌊x/d⌋ + 1` rounds outward: `x + 1 ≤ (up x d) · d`. -/
theorem up_ge (x d : ℕ) (hd : 0 < d) : (x : ℝ) + 1 ≤ (up x d : ℝ) * d := by
  unfold up
  rw [Nat.add_eq, ndiv_eq]
  push_cast
  have := (div_bounds x d hd).2
  linarith

/-- the centre of a product/scalar step: `⌊(hre − lre)/2^48⌋` is within one ulp below `(hre − lre)/2^48` -/
theorem center_bounds (hre lre : ℕ) (h : lre ≤ hre) :
    (((hre - lre) / 281474976710656 : ℕ) : ℝ) * 281474976710656 ≤ (hre : ℝ) - lre ∧
    (hre : ℝ) - lre + 1 ≤ (((hre - lre) / 281474976710656 : ℕ) : ℝ) * 281474976710656 + 281474976710656 := by
  have := div_bounds (hre - lre) 281474976710656 (by norm_num)
  rwa [Nat.cast_sub h] at this

theorem dist_cast (V : ℕ) : (dist V : ℝ) = |(V : ℝ) - 72057594037927936| := by
  unfold dist
  simp only [Nat.add_eq, Nat.sub_eq]
  rcases le_total V 72057594037927936 with h | h
  · have h' : (V : ℝ) ≤ 72057594037927936 := by exact_mod_cast h
    have h'' : (V : ℝ) - 72057594037927936 ≤ 0 := by linarith
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos h'']
    push_cast
    ring
  · have h' : (72057594037927936 : ℝ) ≤ V := by exact_mod_cast h
    have h'' : 0 ≤ (V : ℝ) - 72057594037927936 := by linarith
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg h'']
    push_cast
    ring

theorem abs_add_of {X Y u v : ℝ} (hX : |X| ≤ u) (hY : |Y| ≤ v) : |X + Y| ≤ u + v := by
  obtain ⟨a1, a2⟩ := abs_le.mp hX
  obtain ⟨b1, b2⟩ := abs_le.mp hY
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_sub_of {X Y u v : ℝ} (hX : |X| ≤ u) (hY : |Y| ≤ v) : |X - Y| ≤ u + v := by
  obtain ⟨a1, a2⟩ := abs_le.mp hX
  obtain ⟨b1, b2⟩ := abs_le.mp hY
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- divide an absolute bound by the scale `2^48` -/
theorem abs_scale {t u : ℝ} (h : |281474976710656 * t| ≤ 281474976710656 * u) : |t| ≤ u := by
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 281474976710656)] at h
  exact le_of_mul_le_mul_left h (by norm_num)

/-- `|2^48·(t/j) − c| ≤ m` from `|2^48·t − j·c| ≤ m·j` -/
theorem abs_div_le {t c m j : ℝ} (hj : 0 < j) (h : |281474976710656 * t - j * c| ≤ m * j) :
    |281474976710656 * (t / j) - c| ≤ m := by
  have hj0 : j ≠ 0 := hj.ne'
  have e : 281474976710656 * (t / j) - c = (281474976710656 * t - j * c) / j := by
    field_simp
  rw [e, abs_div, abs_of_pos hj, div_le_iff₀ hj]
  exact h

theorem abs3 (x y e f dr dq : ℝ) (he : |e| ≤ dr) (hf : |f| ≤ dq) :
    |x * f + e * y + e * f| ≤ |x| * dq + dr * |y| + dr * dq := by
  have hdr : 0 ≤ dr := le_trans (abs_nonneg _) he
  have h1 : |x * f| ≤ |x| * dq := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf (abs_nonneg x)
  have h2 : |e * y| ≤ dr * |y| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right he (abs_nonneg y)
  have h3 : |e * f| ≤ dr * dq := by
    rw [abs_mul]; exact mul_le_mul he hf (abs_nonneg f) hdr
  have h4 := abs_add_le (x * f + e * y) (e * f)
  have h5 := abs_add_le (x * f) (e * y)
  linarith

/-- error of a product of two enclosed complex numbers, real and imaginary parts -/
theorem prod_err (Ar Ai Cr Ci er ei fr fi r q : ℝ) (her : |er| ≤ r) (hei : |ei| ≤ r)
    (hfr : |fr| ≤ q) (hfi : |fi| ≤ q) :
    |(Ar + er) * (Cr + fr) - (Ai + ei) * (Ci + fi) - (Ar * Cr - Ai * Ci)| ≤
        (|Ar| + |Ai|) * q + (|Cr| + |Ci|) * r + 2 * r * q ∧
    |(Ar + er) * (Ci + fi) + (Ai + ei) * (Cr + fr) - (Ar * Ci + Ai * Cr)| ≤
        (|Ar| + |Ai|) * q + (|Cr| + |Ci|) * r + 2 * r * q := by
  have h1 := abs3 Ar Cr er fr r q her hfr
  have h2 := abs3 Ai Ci ei fi r q hei hfi
  have h3 := abs3 Ar Ci er fi r q her hfi
  have h4 := abs3 Ai Cr ei fr r q hei hfr
  constructor
  · have e : (Ar + er) * (Cr + fr) - (Ai + ei) * (Ci + fi) - (Ar * Cr - Ai * Ci) =
        (Ar * fr + er * Cr + er * fr) - (Ai * fi + ei * Ci + ei * fi) := by ring
    rw [e]
    have := abs_sub_of h1 h2
    linarith
  · have e : (Ar + er) * (Ci + fi) + (Ai + ei) * (Cr + fr) - (Ar * Ci + Ai * Cr) =
        (Ar * fi + er * Ci + er * fi) + (Ai * fr + ei * Cr + ei * fr) := by ring
    rw [e]
    have := abs_add_of h3 h4
    linarith

/-! ## Flag lemmas: a true flag on a result means true flags on the inputs -/

theorem cmul_v {x y : NB} (h : (cmul x y).v = true) : x.v = true ∧ y.v = true := by
  rw [cmul_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem cadd_v {x y : NB} (h : (cadd x y).v = true) : x.v = true ∧ y.v = true := by
  rw [cadd_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem cdivn_v {x : NB} {j : ℕ} (h : (cdivn x j).v = true) : x.v = true := by
  rw [cdivn_eq] at h
  exact h

theorem horner_v (z : NB) : ∀ (j : ℕ) (acc : NB), (horner z j acc).v = true → acc.v = true := by
  intro j
  induction j with
  | zero => intro acc h; rw [horner_zero] at h; exact h
  | succ j ih =>
    intro acc h
    rw [horner_succ'] at h
    have h2 := ih _ h
    rw [hstep_eq] at h2
    exact (cmul_v (cdivn_v (cadd_v h2).2)).2

theorem sqn_v : ∀ (k : ℕ) (x : NB), (sqn k x).v = true → x.v = true := by
  intro k
  induction k with
  | zero => intro x h; rw [sqn_zero] at h; exact h
  | succ k ih =>
    intro x h
    rw [sqn_succ'] at h
    exact (cmul_v (ih _ h)).1

/-! ## Soundness of the ball operations -/

theorem one_mem : one.Mem 1 := by
  simp only [one, NB.Mem, Complex.one_re, Complex.one_im]
  norm_num

theorem cadd_mem {x y : NB} {z w : ℂ} (hv : (cadd x y).v = true) (hx : x.Mem z) (hy : y.Mem w) :
    (cadd x y).Mem (z + w) := by
  rw [cadd_eq] at hv ⊢
  simp only [NB.Mem, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.sub_eq] at hv hx hy ⊢
  obtain ⟨⟨-, h1⟩, h2⟩ := hv
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Complex.add_re, Complex.add_im]
  push_cast
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · obtain ⟨a1, a2⟩ := abs_le.mp hx1
    obtain ⟨b1, b2⟩ := abs_le.mp hy1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · obtain ⟨a1, a2⟩ := abs_le.mp hx2
    obtain ⟨b1, b2⟩ := abs_le.mp hy2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem csub_mem {x y : NB} {z w : ℂ} (hv : (csub x y).v = true) (hx : x.Mem z) (hy : y.Mem w) :
    (csub x y).Mem (z - w) := by
  rw [csub_eq] at hv ⊢
  simp only [NB.Mem, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.sub_eq] at hv hx hy ⊢
  obtain ⟨⟨-, h1⟩, h2⟩ := hv
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Complex.sub_re, Complex.sub_im]
  push_cast
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · obtain ⟨a1, a2⟩ := abs_le.mp hx1
    obtain ⟨b1, b2⟩ := abs_le.mp hy1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · obtain ⟨a1, a2⟩ := abs_le.mp hx2
    obtain ⟨b1, b2⟩ := abs_le.mp hy2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `cdivn` divides the centre by `j` (rounding to nearest-below of the offset value) and takes the
radius `⌈r/j⌉ + 1`: one ulp for the floor, and the ceiling makes `r/j ≤ ⌈r/j⌉` (review finding 3). -/
theorem cdivn_mem {x : NB} {j : ℕ} {z : ℂ} (hj : 0 < j) (_hv : (cdivn x j).v = true) (hx : x.Mem z) :
    (cdivn x j).Mem (z / (j : ℂ)) := by
  rw [cdivn_eq]
  simp only [NB.Mem, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ndiv_eq] at hx ⊢
  obtain ⟨hx1, hx2⟩ := hx
  rw [Complex.div_natCast_re, Complex.div_natCast_im]
  have hj' : (0:ℝ) < j := by exact_mod_cast hj
  have hj1 : ((j - 1 : ℕ) : ℝ) = j - 1 := Nat.cast_pred hj
  have hr := div_bounds (x.r + (j - 1)) j hj
  have ha := div_bounds (x.a + (j - 1) * 72057594037927936) j hj
  have hb := div_bounds (x.b + (j - 1) * 72057594037927936) j hj
  push_cast [hj1] at hr ha hb ⊢
  obtain ⟨r1, r2⟩ := hr
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  constructor
  · refine abs_div_le hj' ?_
    obtain ⟨c1, c2⟩ := abs_le.mp hx1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine abs_div_le hj' ?_
    obtain ⟨c1, c2⟩ := abs_le.mp hx2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cmul_mem {x y : NB} {z w : ℂ} (hv : (cmul x y).v = true) (hx : x.Mem z) (hy : y.Mem w) :
    (cmul x y).Mem (z * w) := by
  rw [cmul_eq] at hv ⊢
  simp only [NB.Mem, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
    ndiv_eq] at hv hx hy ⊢
  obtain ⟨⟨-, h1⟩, h2⟩ := hv
  rw [Complex.mul_re, Complex.mul_im]
  have hre := center_bounds _ _ h1
  have him := center_bounds _ _ h2
  have hu := up_ge ((dist x.a + dist x.b) * y.r + (dist y.a + dist y.b) * x.r + 2 * (x.r * y.r))
    281474976710656 (by norm_num)
  push_cast at hre him hu ⊢
  simp only [dist_cast] at hu
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hp := prod_err ((x.a:ℝ) - 72057594037927936) ((x.b:ℝ) - 72057594037927936)
    ((y.a:ℝ) - 72057594037927936) ((y.b:ℝ) - 72057594037927936) _ _ _ _ (x.r : ℝ) (y.r : ℝ)
    hx1 hx2 hy1 hy2
  obtain ⟨p1, p2⟩ := hp
  obtain ⟨a1, a2⟩ := abs_le.mp p1
  obtain ⟨b1, b2⟩ := abs_le.mp p2
  obtain ⟨r1, r2⟩ := hre
  obtain ⟨i1, i2⟩ := him
  constructor
  · apply abs_scale
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · apply abs_scale
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `rmul L w` encloses `ℓ · z` whenever `|2^48·ℓ − L| ≤ 1` and `w` encloses `z`. -/
theorem rmul_mem {L : ℕ} {w : NB} {ℓ : ℝ} {z : ℂ} (hL : |281474976710656 * ℓ - L| ≤ 1)
    (hv : (rmul L w).v = true) (hw : w.Mem z) : (rmul L w).Mem ((ℓ : ℂ) * z) := by
  rw [rmul_eq] at hv ⊢
  simp only [NB.Mem, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
    ndiv_eq] at hv hw ⊢
  obtain ⟨⟨-, h1⟩, h2⟩ := hv
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have ha := center_bounds _ _ h1
  have hb := center_bounds _ _ h2
  have hu := up_ge (L * w.r + dist w.a + dist w.b + w.r) 281474976710656 (by norm_num)
  push_cast at ha hb hu ⊢
  simp only [dist_cast] at hu
  obtain ⟨hw1, hw2⟩ := hw
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg L
  have p1 : |(L:ℝ) * (281474976710656 * z.re - ((w.a:ℝ) - 72057594037927936))| ≤ L * w.r := by
    rw [abs_mul, abs_of_nonneg hL0]; exact mul_le_mul_of_nonneg_left hw1 hL0
  have p2 : |(281474976710656 * ℓ - L) * ((w.a:ℝ) - 72057594037927936)| ≤
      |(w.a:ℝ) - 72057594037927936| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hL
  have p3 : |(281474976710656 * ℓ - L) * (281474976710656 * z.re - ((w.a:ℝ) - 72057594037927936))| ≤
      w.r := by
    rw [abs_mul]
    calc _ ≤ 1 * (w.r:ℝ) := mul_le_mul hL hw1 (abs_nonneg _) zero_le_one
      _ = w.r := one_mul _
  have q1 : |(L:ℝ) * (281474976710656 * z.im - ((w.b:ℝ) - 72057594037927936))| ≤ L * w.r := by
    rw [abs_mul, abs_of_nonneg hL0]; exact mul_le_mul_of_nonneg_left hw2 hL0
  have q2 : |(281474976710656 * ℓ - L) * ((w.b:ℝ) - 72057594037927936)| ≤
      |(w.b:ℝ) - 72057594037927936| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hL
  have q3 : |(281474976710656 * ℓ - L) * (281474976710656 * z.im - ((w.b:ℝ) - 72057594037927936))| ≤
      w.r := by
    rw [abs_mul]
    calc _ ≤ 1 * (w.r:ℝ) := mul_le_mul hL hw2 (abs_nonneg _) zero_le_one
      _ = w.r := one_mul _
  obtain ⟨a1, a2⟩ := abs_le.mp p1
  obtain ⟨b1, b2⟩ := abs_le.mp p2
  obtain ⟨c1, c2⟩ := abs_le.mp p3
  obtain ⟨d1, d2⟩ := abs_le.mp q1
  obtain ⟨e1, e2⟩ := abs_le.mp q2
  obtain ⟨f1, f2⟩ := abs_le.mp q3
  obtain ⟨r1, r2⟩ := ha
  obtain ⟨i1, i2⟩ := hb
  constructor
  · apply abs_scale
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · apply abs_scale
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## Horner, exp, squaring -/

/-- `horner z j acc` encloses `Σ_{m<j} ζ^m/m! + α·ζ^j/j!` when `z` encloses `ζ` and `acc` encloses `α`. -/
theorem horner_mem {z : NB} {ζ : ℂ} (hz : z.Mem ζ) : ∀ (j : ℕ) (acc : NB) (α : ℂ),
    (horner z j acc).v = true → acc.Mem α →
    (horner z j acc).Mem
      (∑ m ∈ Finset.range j, ζ ^ m / (m.factorial : ℂ) + α * ζ ^ j / (j.factorial : ℂ)) := by
  intro j
  induction j with
  | zero =>
    intro acc α hv ha
    rw [horner_zero]
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, div_one, zero_add]
    exact ha
  | succ j ih =>
    intro acc α hv ha
    rw [horner_succ'] at hv ⊢
    have hacc' : (hstep z j acc).v = true := horner_v z j _ hv
    rw [hstep_eq] at hacc'
    have h1 : (cmul z acc).Mem (ζ * α) := cmul_mem (cdivn_v (cadd_v hacc').2) hz ha
    have h2 : (cdivn (cmul z acc) (j + 1)).Mem (ζ * α / ((j + 1 : ℕ) : ℂ)) :=
      cdivn_mem (Nat.succ_pos j) (cadd_v hacc').2 h1
    have h3 : (cadd one (cdivn (cmul z acc) (j + 1))).Mem (1 + ζ * α / ((j + 1 : ℕ) : ℂ)) :=
      cadd_mem hacc' one_mem h2
    rw [← hstep_eq] at h3
    have h4 := ih (hstep z j acc) _ hv h3
    have e : ∑ m ∈ Finset.range j, ζ ^ m / (m.factorial : ℂ) +
          (1 + ζ * α / ((j + 1 : ℕ) : ℂ)) * ζ ^ j / (j.factorial : ℂ) =
        ∑ m ∈ Finset.range (j + 1), ζ ^ m / (m.factorial : ℂ) +
          α * ζ ^ (j + 1) / ((j + 1).factorial : ℂ) := by
      rw [Finset.sum_range_succ, Nat.factorial_succ, Nat.cast_mul]
      ring
    rw [← e]
    exact h4

theorem norm_le_ubz {z : NB} {ζ : ℂ} (hz : z.Mem ζ) : ‖ζ‖ * 281474976710656 ≤ (ubz z : ℝ) := by
  unfold ubz
  simp only [NB.Mem, Nat.add_eq, Nat.mul_eq] at hz ⊢
  push_cast
  simp only [dist_cast]
  obtain ⟨h1, h2⟩ := hz
  have e1 := abs_sub_abs_le_abs_sub (281474976710656 * ζ.re) ((z.a:ℝ) - 72057594037927936)
  have e2 := abs_sub_abs_le_abs_sub (281474976710656 * ζ.im) ((z.b:ℝ) - 72057594037927936)
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 281474976710656)] at e1 e2
  have := Complex.norm_le_abs_re_add_abs_im ζ
  linarith

/-- `remb u` dominates `2^48 · t^16 · 17/(16!·16)` whenever `t · 2^48 ≤ u`: the `exp_bound` remainder
(n = 16) in ulps, rounded outward at both floors. -/
theorem remb_ge (u : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t * 281474976710656 ≤ u) :
    281474976710656 * (t ^ 16 * (17 / 334764638208000)) ≤ (remb u : ℝ) := by
  unfold remb
  generalize hq0 : Nat.shiftRight (Nat.pow u 16) 720 = q
  have hq : q = u ^ 16 / 2 ^ 720 := by
    rw [← hq0]; exact Nat.shiftRight_eq_div_pow (Nat.pow u 16) 720
  have hb := div_bounds (u ^ 16) (2 ^ 720) (by positivity)
  rw [← hq] at hb
  have hR := up_ge (Nat.mul (Nat.add q 1) 17) 334764638208000 (by norm_num)
  simp only [Nat.add_eq, Nat.mul_eq] at hR ⊢
  push_cast at hb hR ⊢
  obtain ⟨q1, q2⟩ := hb
  have ht16 : (t * 281474976710656) ^ 16 ≤ (u : ℝ) ^ 16 := pow_le_pow_left₀ (by positivity) ht 16
  rw [mul_pow] at ht16
  have hS : (281474976710656 : ℝ) ^ 16 = 281474976710656 * 2 ^ 720 := by
    have h48 : (281474976710656 : ℝ) = 2 ^ 48 := by norm_num
    rw [h48, ← pow_mul, ← pow_add]
  rw [hS] at ht16
  have h3 : 281474976710656 * t ^ 16 * 2 ^ 720 ≤ ((q : ℝ) + 1) * 2 ^ 720 := by
    linarith
  have h4 : 281474976710656 * t ^ 16 ≤ (q : ℝ) + 1 :=
    le_of_mul_le_mul_right h3 (by positivity)
  have e : 281474976710656 * (t ^ 16 * (17 / 334764638208000)) =
      (281474976710656 * t ^ 16 * 17) / 334764638208000 := by ring
  rw [e, div_le_iff₀ (by norm_num)]
  have h5 : 281474976710656 * t ^ 16 * 17 ≤ ((q : ℝ) + 1) * 17 :=
    mul_le_mul_of_nonneg_right h4 (by norm_num)
  have h6 : ((q : ℝ) + 1) * 17 ≤ ((q : ℝ) + 1) * 17 + 1 := by linarith
  exact h5.trans (h6.trans hR)

/-- `cexp z` encloses `exp ζ`: the degree-15 Horner polynomial plus `Complex.exp_bound` with n = 16. -/
theorem cexp_mem {z : NB} {ζ : ℂ} (hv : (cexp z).v = true) (hz : z.Mem ζ)
    (hub : ubz z ≤ 281474976710656) : (cexp z).Mem (Complex.exp ζ) := by
  obtain ⟨⟨a, b, r, v⟩, hH⟩ : ∃ H, horner z 15 one = H := ⟨_, rfl⟩
  rw [cexp_eq z a b r v hH] at hv ⊢
  have hv' : (horner z 15 one).v = true := by rw [hH]; exact hv
  have hP := horner_mem hz 15 one 1 hv' one_mem
  rw [hH] at hP
  have eP : ∑ m ∈ Finset.range 15, ζ ^ m / (m.factorial : ℂ) + 1 * ζ ^ 15 / ((15 : ℕ).factorial : ℂ) =
      ∑ m ∈ Finset.range 16, ζ ^ m / (m.factorial : ℂ) := by
    rw [Finset.sum_range_succ _ 15, one_mul]
  rw [eP] at hP
  have hn := norm_le_ubz hz
  have hub' : (ubz z : ℝ) ≤ 281474976710656 := by exact_mod_cast hub
  have hζ1 : ‖ζ‖ ≤ 1 := by linarith
  have hE : ‖Complex.exp ζ - ∑ m ∈ Finset.range 16, ζ ^ m / (m.factorial : ℂ)‖ ≤
      ‖ζ‖ ^ 16 * (17 / 334764638208000) := by
    have h := Complex.exp_bound hζ1 (n := 16) (by norm_num)
    have hf : ((Nat.factorial 16 : ℕ) : ℝ) = 20922789888000 := by
      rw [show Nat.factorial 16 = 20922789888000 from rfl]; norm_num
    refine h.trans (le_of_eq ?_)
    rw [hf]
    push_cast
    ring
  have hrb := remb_ge (ubz z) ‖ζ‖ (norm_nonneg ζ) hn
  have hre := Complex.abs_re_le_norm
    (Complex.exp ζ - ∑ m ∈ Finset.range 16, ζ ^ m / (m.factorial : ℂ))
  have him := Complex.abs_im_le_norm
    (Complex.exp ζ - ∑ m ∈ Finset.range 16, ζ ^ m / (m.factorial : ℂ))
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  simp only [NB.Mem, Nat.add_eq] at hP ⊢
  push_cast
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨a1, a2⟩ := abs_le.mp hP1
  obtain ⟨b1, b2⟩ := abs_le.mp hP2
  obtain ⟨c1, c2⟩ := abs_le.mp hre
  obtain ⟨d1, d2⟩ := abs_le.mp him
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `sqn k x` encloses `ζ ^ (2^k)` when `x` encloses `ζ`. -/
theorem sqn_mem : ∀ (k : ℕ) (x : NB) (ζ : ℂ), (sqn k x).v = true → x.Mem ζ →
    (sqn k x).Mem (ζ ^ (2 ^ k)) := by
  intro k
  induction k with
  | zero =>
    intro x ζ hv hx
    rw [sqn_zero, pow_zero, pow_one]
    exact hx
  | succ k ih =>
    intro x ζ hv hx
    rw [sqn_succ'] at hv ⊢
    have h1 : (cmul x x).Mem (ζ * ζ) := cmul_mem (sqn_v k _ hv) hx hx
    have h2 := ih (cmul x x) (ζ * ζ) hv h1
    rw [pow_succ', pow_mul, pow_two]
    exact h2

/-! ## Stage S2 kernel-side definitions (mirror: `sim/zbox_sound4.py`; probe text `sim/emit_sound4.py`)

Constants: `S = 2^48 = 281474976710656`, `O = 2^56 = 72057594037927936`, `S^2 = 79228162514264337593543950336`,
`9·O = 648518346341351424`, `64·S = 18014398509481984`, `2·S = 562949953421312`,
`L10 + 1 = 648120085424804`, `N·N·240 = 24000`, `12·N = 120`.  The logs `L_n = round(2^48 · log n)`
(`n = 2..10`) are the literals 195103586505167, 309231868366897, 390207173010335, 453016498919635,
504335454872064, 547725013886373, 585310759515502, 618463736733793, 648120085424803. -/

/-- the ball for `−c·log n/64` (`c = (SC + i·TC)/2^48`), given `|2^48·log n − L| ≤ 1` -/
def zarg (L SC TC : Nat) : NB :=
  match Nat.shiftRight (Nat.mul SC L) 54, Nat.shiftRight (Nat.mul TC L) 54 with
  | p, q => ⟨Nat.sub 72057594037927936 p, Nat.sub 72057594037927936 q, 3,
             Nat.ble p 72057594037927936 && Nat.ble q 72057594037927936⟩

/-- an upper bound for `2^48·|w|` over the ball: `max + min/2 + 1 + 2r` -/
def magub (w : NB) : Nat :=
  if Nat.blt (dist w.a) (dist w.b) then
    Nat.add (Nat.add (Nat.add (dist w.b) (Nat.div (dist w.a) 2)) 1) (Nat.mul 2 w.r)
  else Nat.add (Nat.add (Nat.add (dist w.a) (Nat.div (dist w.b) 2)) 1) (Nat.mul 2 w.r)

structure Acc where
  F : NB
  q : Nat
  w : NB
  ok : Bool
  dS : NB

/-- `n^(−c) = exp(−c·log n/64)^64` -/
def epow (L SC TC : Nat) : NB := sqn 6 (cexp (zarg L SC TC))
def zok (L SC TC : Nat) : Bool := Nat.ble (ubz (zarg L SC TC)) 281474976710656

/-- one Dirichlet term: `F += w`, `dS += (log n)·w`, `q += ⌈|w|·x²⌉` with `x ≥ 2^48·ρ·log n` -/
def term (rho L : Nat) (w : NB) (acc : Acc) : Acc :=
  match up (Nat.mul rho (Nat.add L 1)) 281474976710656 with
  | x => ⟨cadd acc.F w,
          Nat.add acc.q (up (Nat.mul (magub w) (up (Nat.mul x x) 281474976710656)) 281474976710656),
          w, acc.ok && Nat.ble x 281474976710656, cadd acc.dS (rmul L w)⟩

def acc0 (ok0 : Bool) : Acc :=
  ⟨one, 0, one, ok0, ⟨72057594037927936, 72057594037927936, 0, true⟩⟩

/-- the sum over `n = 2..10`; 4, 6, 8, 9, 10 are ball products of the prime powers -/
def accOf (rho SC TC : Nat) (w2 w3 w5 w7 : NB) : Acc :=
  term rho 648120085424803 (cmul w2 w5) (term rho 618463736733793 (cmul w3 w3)
  (term rho 585310759515502 (cmul (cmul w2 w2) w2) (term rho 547725013886373 w7
  (term rho 504335454872064 (cmul w2 w3) (term rho 453016498919635 w5
  (term rho 390207173010335 (cmul w2 w2) (term rho 309231868366897 w3
  (term rho 195103586505167 w2 (acc0 (zok 195103586505167 SC TC && zok 309231868366897 SC TC &&
    zok 453016498919635 SC TC && zok 547725013886373 SC TC))))))))))

/-- the ball for `1/(1−c)` -/
def invB (SC TC : Nat) : NB :=
  match Nat.sub 281474976710656 SC with
  | ar =>
  match Nat.add (Nat.mul ar ar) (Nat.mul TC TC) with
  | D => ⟨Nat.add (Nat.div (Nat.mul ar 79228162514264337593543950336) D) 72057594037927936,
          Nat.add (Nat.div (Nat.mul TC 79228162514264337593543950336) D) 72057594037927936, 1, true⟩

/-- `10·w` -/
def nmul (w : NB) : NB :=
  match Nat.mul 10 w.a, Nat.mul 10 w.b with
  | na, nb => ⟨Nat.sub na 648518346341351424, Nat.sub nb 648518346341351424, Nat.mul 10 w.r,
               w.v && Nat.ble 648518346341351424 na && Nat.ble 648518346341351424 nb⟩

def T1of (SC TC : Nat) (wN : NB) : NB := cmul (nmul wN) (invB SC TC)

/-- `F(c) = F0 − 10·w/(1−c) − w/2 + c·w/120` -/
def Fof (SC TC : Nat) (F0 wN : NB) : NB :=
  cadd (csub (csub F0 (T1of SC TC wN)) (cdivn wN 2))
    (cdivn (cmul ⟨Nat.add 72057594037927936 SC, Nat.add 72057594037927936 TC, 0, true⟩ wN) 120)

def xNof (rho : Nat) : Nat := up (Nat.mul rho 648120085424804) 281474976710656
def gNof (rho : Nat) : Nat :=
  Nat.add (xNof rho) (up (Nat.mul (xNof rho) (xNof rho)) 281474976710656)
def bL1 (TC RT rho mN : Nat) : Nat :=
  up (Nat.mul (Nat.mul 10 mN) (Nat.add (gNof rho) (up (Nat.mul rho 281474976710656) TC))) (Nat.sub TC RT)
def bL2 (rho mN : Nat) : Nat := up (Nat.mul mN (gNof rho)) 562949953421312
def bL3 (SC TC rho mN : Nat) : Nat :=
  up (Nat.add (up (Nat.mul (up (Nat.mul rho mN) 281474976710656) (Nat.add 281474976710656 (gNof rho))) 281474976710656)
              (up (Nat.mul (up (Nat.mul (Nat.add SC TC) mN) 281474976710656) (gNof rho)) 281474976710656)) 120
def Uk (tmax sk : Nat) : Nat := Nat.add tmax (up (Nat.mul sk sk) (Nat.mul 2 tmax))
def nsmOf (RS mN : Nat) : Nat :=
  match up (Nat.mul RS 648120085424804) 281474976710656 with
  | xs => up (Nat.mul mN (Nat.add (Nat.add 281474976710656 xs) (up (Nat.mul xs xs) 281474976710656))) 281474976710656
def bE (SC TC RS RT mN : Nat) : Nat :=
  match Nat.add TC RT, Nat.add SC RS with
  | tmax, smax =>
  up (up (Nat.mul (up (Nat.mul (up (Nat.mul (Uk tmax smax) (Uk tmax (Nat.add smax 281474976710656))) 281474976710656)
      (Uk tmax (Nat.add smax 562949953421312))) 281474976710656) (nsmOf RS mN)) 281474976710656) 24000
def bD1 (rho : Nat) (dS : NB) : Nat := up (Nat.mul rho (magub dS)) 281474976710656
def boundT (SC TC RS RT q : Nat) (wN dS : NB) : Nat :=
  match Nat.add RS RT, magub wN with
  | rho, mN => Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q (bL1 TC RT rho mN)) (bL2 rho mN))
      (bL3 SC TC rho mN)) (bE SC TC RS RT mN)) (bD1 rho dS)

/-- the order-1.5 test of `sim/zbox_sound4.py`, given the accumulated Dirichlet sum -/
def boxT (SC TC RS RT : Nat) (acc : Acc) : Bool :=
  match Fof SC TC acc.F acc.w, boundT SC TC RS RT acc.q acc.w acc.dS with
  | F, T =>
  match Nat.sub (dist F.a) F.r, Nat.sub (dist F.b) F.r with
  | fr, fi =>
    acc.ok && F.v && acc.dS.v && (T1of SC TC acc.w).v && Nat.ble (Nat.add SC RS) 281474976710656 &&
    Nat.ble TC 18014398509481984 && Nat.blt RT TC && Nat.ble (xNof (Nat.add RS RT)) 281474976710656 &&
    Nat.blt (Nat.mul T T) (Nat.add (Nat.mul fr fr) (Nat.mul fi fi))

/-- the box `|2^48·Re s − SC| ≤ RS`, `|2^48·Im s − TC| ≤ RT` has no zero of ζ -/
def boxN (SC TC RS RT : Nat) : Bool :=
  boxT SC TC RS RT (accOf (Nat.add RS RT) SC TC (epow 195103586505167 SC TC) (epow 309231868366897 SC TC)
    (epow 453016498919635 SC TC) (epow 547725013886373 SC TC))

inductive QT where
  | leaf : QT
  | node : QT → QT → QT → QT → QT

/-- `qtOK q x0 y0 j`: the square `[x0, x0 + 2^(j+1)] × [y0, y0 + 2^(j+1)]` (in ulps) is covered by
the leaves of `q`, each of which passes `boxN` -/
def qtOK : QT → Nat → Nat → Nat → Bool
  | QT.leaf, x0, y0, j => boxN (Nat.add x0 (Nat.pow 2 j)) (Nat.add y0 (Nat.pow 2 j)) (Nat.pow 2 j) (Nat.pow 2 j)
  | QT.node a b c d, x0, y0, j =>
    match j with
    | 0 => false
    | k + 1 => qtOK a x0 y0 k && qtOK b (Nat.add x0 (Nat.pow 2 (k + 1))) y0 k &&
        qtOK c x0 (Nat.add y0 (Nat.pow 2 (k + 1))) k &&
        qtOK d (Nat.add x0 (Nat.pow 2 (k + 1))) (Nat.add y0 (Nat.pow 2 (k + 1))) k

/-! ## S2 structure equations (proved by `rfl`; the proofs below open the S2 defs only through these) -/

theorem zarg_eq (L SC TC : Nat) : zarg L SC TC =
    ⟨Nat.sub 72057594037927936 (Nat.shiftRight (Nat.mul SC L) 54),
     Nat.sub 72057594037927936 (Nat.shiftRight (Nat.mul TC L) 54), 3,
     Nat.ble (Nat.shiftRight (Nat.mul SC L) 54) 72057594037927936 &&
       Nat.ble (Nat.shiftRight (Nat.mul TC L) 54) 72057594037927936⟩ := rfl

theorem magub_eq (w : NB) : magub w = if Nat.blt (dist w.a) (dist w.b) = true then
      Nat.add (Nat.add (Nat.add (dist w.b) (Nat.div (dist w.a) 2)) 1) (Nat.mul 2 w.r)
    else Nat.add (Nat.add (Nat.add (dist w.a) (Nat.div (dist w.b) 2)) 1) (Nat.mul 2 w.r) := rfl

theorem epow_eq (L SC TC : Nat) : epow L SC TC = sqn 6 (cexp (zarg L SC TC)) := rfl

theorem zok_eq (L SC TC : Nat) : zok L SC TC = Nat.ble (ubz (zarg L SC TC)) 281474976710656 := rfl

theorem term_eq (rho L : Nat) (w : NB) (acc : Acc) : term rho L w acc =
    ⟨cadd acc.F w,
     Nat.add acc.q (up (Nat.mul (magub w) (up (Nat.mul (up (Nat.mul rho (Nat.add L 1)) 281474976710656)
       (up (Nat.mul rho (Nat.add L 1)) 281474976710656)) 281474976710656)) 281474976710656),
     w, acc.ok && Nat.ble (up (Nat.mul rho (Nat.add L 1)) 281474976710656) 281474976710656,
     cadd acc.dS (rmul L w)⟩ := rfl

theorem acc0_eq (ok0 : Bool) : acc0 ok0 =
    ⟨one, 0, one, ok0, ⟨72057594037927936, 72057594037927936, 0, true⟩⟩ := rfl

theorem accOf_eq (rho SC TC : Nat) (w2 w3 w5 w7 : NB) : accOf rho SC TC w2 w3 w5 w7 =
    term rho 648120085424803 (cmul w2 w5) (term rho 618463736733793 (cmul w3 w3)
    (term rho 585310759515502 (cmul (cmul w2 w2) w2) (term rho 547725013886373 w7
    (term rho 504335454872064 (cmul w2 w3) (term rho 453016498919635 w5
    (term rho 390207173010335 (cmul w2 w2) (term rho 309231868366897 w3
    (term rho 195103586505167 w2 (acc0 (zok 195103586505167 SC TC && zok 309231868366897 SC TC &&
      zok 453016498919635 SC TC && zok 547725013886373 SC TC)))))))))) := rfl

theorem invB_eq (SC TC : Nat) : invB SC TC =
    ⟨Nat.add (Nat.div (Nat.mul (Nat.sub 281474976710656 SC) 79228162514264337593543950336)
        (Nat.add (Nat.mul (Nat.sub 281474976710656 SC) (Nat.sub 281474976710656 SC)) (Nat.mul TC TC)))
        72057594037927936,
     Nat.add (Nat.div (Nat.mul TC 79228162514264337593543950336)
        (Nat.add (Nat.mul (Nat.sub 281474976710656 SC) (Nat.sub 281474976710656 SC)) (Nat.mul TC TC)))
        72057594037927936, 1, true⟩ := rfl

theorem nmul_eq (w : NB) : nmul w =
    ⟨Nat.sub (Nat.mul 10 w.a) 648518346341351424, Nat.sub (Nat.mul 10 w.b) 648518346341351424,
     Nat.mul 10 w.r,
     w.v && Nat.ble 648518346341351424 (Nat.mul 10 w.a) && Nat.ble 648518346341351424 (Nat.mul 10 w.b)⟩ :=
  rfl

theorem T1of_eq (SC TC : Nat) (wN : NB) : T1of SC TC wN = cmul (nmul wN) (invB SC TC) := rfl

theorem Fof_eq (SC TC : Nat) (F0 wN : NB) : Fof SC TC F0 wN =
    cadd (csub (csub F0 (T1of SC TC wN)) (cdivn wN 2))
      (cdivn (cmul ⟨Nat.add 72057594037927936 SC, Nat.add 72057594037927936 TC, 0, true⟩ wN) 120) := rfl

theorem nsmOf_eq (RS mN : Nat) : nsmOf RS mN =
    up (Nat.mul mN (Nat.add (Nat.add 281474976710656 (up (Nat.mul RS 648120085424804) 281474976710656))
      (up (Nat.mul (up (Nat.mul RS 648120085424804) 281474976710656)
        (up (Nat.mul RS 648120085424804) 281474976710656)) 281474976710656))) 281474976710656 := rfl

theorem bE_eq (SC TC RS RT mN : Nat) : bE SC TC RS RT mN =
    up (up (Nat.mul (up (Nat.mul (up (Nat.mul (Uk (Nat.add TC RT) (Nat.add SC RS))
        (Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 281474976710656))) 281474976710656)
      (Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 562949953421312))) 281474976710656) (nsmOf RS mN))
      281474976710656) 24000 := rfl

theorem boundT_eq (SC TC RS RT q : Nat) (wN dS : NB) : boundT SC TC RS RT q wN dS =
    Nat.add (Nat.add (Nat.add (Nat.add (Nat.add q (bL1 TC RT (Nat.add RS RT) (magub wN)))
      (bL2 (Nat.add RS RT) (magub wN))) (bL3 SC TC (Nat.add RS RT) (magub wN)))
      (bE SC TC RS RT (magub wN))) (bD1 (Nat.add RS RT) dS) := rfl

theorem boxT_eq (SC TC RS RT : Nat) (acc : Acc) : boxT SC TC RS RT acc =
    (acc.ok && (Fof SC TC acc.F acc.w).v && acc.dS.v && (T1of SC TC acc.w).v &&
      Nat.ble (Nat.add SC RS) 281474976710656 && Nat.ble TC 18014398509481984 && Nat.blt RT TC &&
      Nat.ble (xNof (Nat.add RS RT)) 281474976710656 &&
      Nat.blt (Nat.mul (boundT SC TC RS RT acc.q acc.w acc.dS) (boundT SC TC RS RT acc.q acc.w acc.dS))
        (Nat.add (Nat.mul (Nat.sub (dist (Fof SC TC acc.F acc.w).a) (Fof SC TC acc.F acc.w).r)
                          (Nat.sub (dist (Fof SC TC acc.F acc.w).a) (Fof SC TC acc.F acc.w).r))
                 (Nat.mul (Nat.sub (dist (Fof SC TC acc.F acc.w).b) (Fof SC TC acc.F acc.w).r)
                          (Nat.sub (dist (Fof SC TC acc.F acc.w).b) (Fof SC TC acc.F acc.w).r)))) := rfl

theorem boxN_eq (SC TC RS RT : Nat) : boxN SC TC RS RT =
    boxT SC TC RS RT (accOf (Nat.add RS RT) SC TC (epow 195103586505167 SC TC) (epow 309231868366897 SC TC)
      (epow 453016498919635 SC TC) (epow 547725013886373 SC TC)) := rfl

theorem qtOK_leaf (x0 y0 j : Nat) : qtOK QT.leaf x0 y0 j =
    boxN (Nat.add x0 (Nat.pow 2 j)) (Nat.add y0 (Nat.pow 2 j)) (Nat.pow 2 j) (Nat.pow 2 j) := by
  rw [qtOK]

theorem qtOK_node0 (a b c d : QT) (x0 y0 : Nat) : qtOK (QT.node a b c d) x0 y0 0 = false := by
  rw [qtOK]

theorem qtOK_node (a b c d : QT) (x0 y0 k : Nat) : qtOK (QT.node a b c d) x0 y0 (k + 1) =
    (qtOK a x0 y0 k && qtOK b (Nat.add x0 (Nat.pow 2 (k + 1))) y0 k &&
      qtOK c x0 (Nat.add y0 (Nat.pow 2 (k + 1))) k &&
      qtOK d (Nat.add x0 (Nat.pow 2 (k + 1))) (Nat.add y0 (Nat.pow 2 (k + 1))) k) := by
  rw [qtOK]

theorem csub_v {x y : NB} (h : (csub x y).v = true) : x.v = true ∧ y.v = true := by
  rw [csub_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2⟩


/-! ## S2 semantics, part 1: exponentials, products, `1/(1−c)`, the centre value `F(c)` -/

/-- the box centre `c = (SC + i·TC)/2^48` -/
noncomputable def cof (SC TC : ℕ) : ℂ := ⟨(SC : ℝ) / 281474976710656, (TC : ℝ) / 281474976710656⟩

/-- the Dirichlet term `n^(−z)` -/
noncomputable def W (n : ℕ) (z : ℂ) : ℂ := (n : ℂ) ^ (-z)

theorem W_mul (m n : ℕ) (z : ℂ) : W m z * W n z = W (m * n) z := by
  unfold W
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

/-- `2^48·‖z‖ ≤ X + Y/2` when `(2^48 re)² + (2^48 im)² ≤ X² + Y²` and `0 ≤ Y ≤ X` -/
theorem snorm_le {z : ℂ} {X Y : ℝ} (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (h : (281474976710656 * z.re) ^ 2 + (281474976710656 * z.im) ^ 2 ≤ X ^ 2 + Y ^ 2) :
    281474976710656 * ‖z‖ ≤ X + Y / 2 := by
  have hsq : (281474976710656 * ‖z‖) ^ 2 ≤ (X + Y / 2) ^ 2 := by
    have e : (281474976710656 * ‖z‖) ^ 2 =
        (281474976710656 * z.re) ^ 2 + (281474976710656 * z.im) ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
    rw [e]
    linarith [h, mul_nonneg hY (sub_nonneg.mpr hYX), sq_nonneg Y]
  exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).mp hsq

theorem sq_le_of_abs {u X : ℝ} (h : |u| ≤ X) : u ^ 2 ≤ X ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- the ball bounds `|2^48·Re z| ≤ |a − O| + r`, `|2^48·Im z| ≤ |b − O| + r` -/
theorem mem_abs {x : NB} {z : ℂ} (hx : x.Mem z) :
    |281474976710656 * z.re| ≤ (dist x.a : ℝ) + x.r ∧
      |281474976710656 * z.im| ≤ (dist x.b : ℝ) + x.r := by
  obtain ⟨h1, h2⟩ := hx
  rw [dist_cast, dist_cast]
  constructor
  · have := abs_sub_abs_le_abs_sub (281474976710656 * z.re) ((x.a : ℝ) - 72057594037927936)
    linarith
  · have := abs_sub_abs_le_abs_sub (281474976710656 * z.im) ((x.b : ℝ) - 72057594037927936)
    linarith

theorem half_floor (d : ℕ) : ((d : ℝ) - 1) / 2 ≤ ((d / 2 : ℕ) : ℝ) := by
  have := (div_bounds d 2 (by norm_num)).2
  push_cast at this
  linarith

/-- `magub w ≥ 2^48·|z|` (`√(X² + Y²) ≤ X + Y/2` for `0 ≤ Y ≤ X`) -/
theorem magub_ge {w : NB} {z : ℂ} (hw : w.Mem z) : 281474976710656 * ‖z‖ ≤ (magub w : ℝ) := by
  obtain ⟨h1, h2⟩ := mem_abs hw
  have s1 := sq_le_of_abs h1
  have s2 := sq_le_of_abs h2
  have r0 : (0:ℝ) ≤ w.r := Nat.cast_nonneg _
  have da0 : (0:ℝ) ≤ dist w.a := Nat.cast_nonneg _
  have db0 : (0:ℝ) ≤ dist w.b := Nat.cast_nonneg _
  rw [magub_eq]
  split_ifs with hlt
  · rw [Nat.blt_eq] at hlt
    have hlt' : (dist w.a : ℝ) ≤ dist w.b := by exact_mod_cast hlt.le
    have := snorm_le (X := (dist w.b : ℝ) + w.r) (Y := (dist w.a : ℝ) + w.r) (by linarith)
      (by linarith) (by linarith)
    have hf := half_floor (dist w.a)
    simp only [Nat.add_eq, Nat.mul_eq, ndiv_eq]
    push_cast
    linarith
  · rw [Nat.blt_eq, not_lt] at hlt
    have hlt' : (dist w.b : ℝ) ≤ dist w.a := by exact_mod_cast hlt
    have := snorm_le (X := (dist w.a : ℝ) + w.r) (Y := (dist w.b : ℝ) + w.r) (by linarith)
      (by linarith) (by linarith)
    have hf := half_floor (dist w.b)
    simp only [Nat.add_eq, Nat.mul_eq, ndiv_eq]
    push_cast
    linarith

/-- the zarg coordinate: `|⌊X·L/2^54⌋ − X·log n/64| ≤ 2 ≤ 3` -/
theorem zarg_coord (X L : ℕ) (ℓ : ℝ) (hL : |281474976710656 * ℓ - L| ≤ 1)
    (hX : X ≤ 18014398509481984) (h : (X * L) >>> 54 ≤ 72057594037927936) :
    |281474976710656 * -((X : ℝ) / 281474976710656 * ℓ / 64) -
        (((72057594037927936 - (X * L) >>> 54 : ℕ) : ℝ) - 72057594037927936)| ≤ ((3 : ℕ) : ℝ) := by
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  rw [Nat.cast_sub h]
  have hb := div_bounds (X * L) (2 ^ 54) (by positivity)
  push_cast at hb ⊢
  norm_num at hb ⊢
  obtain ⟨b1, b2⟩ := hb
  have hX' : (X : ℝ) ≤ 18014398509481984 := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  obtain ⟨l1, l2⟩ := abs_le.mp hL
  have m1 : (X : ℝ) * (281474976710656 * ℓ - L) ≤ X := by
    linarith [mul_nonneg hX0 (by linarith : (0 : ℝ) ≤ 1 - (281474976710656 * ℓ - L))]
  have m2 : -(X : ℝ) ≤ X * (281474976710656 * ℓ - L) := by
    linarith [mul_nonneg hX0 (by linarith : (0 : ℝ) ≤ (281474976710656 * ℓ - L) + 1)]
  rw [abs_le]
  constructor <;> linarith

/-- `zarg` encloses `−c·log n/64` -/
theorem zarg_mem {L SC TC : ℕ} {ℓ : ℝ} (hL : |281474976710656 * ℓ - L| ≤ 1)
    (hSC : SC ≤ 18014398509481984) (hTC : TC ≤ 18014398509481984) (hv : (zarg L SC TC).v = true) :
    (zarg L SC TC).Mem ⟨-((SC : ℝ) / 281474976710656 * ℓ / 64), -((TC : ℝ) / 281474976710656 * ℓ / 64)⟩ := by
  rw [zarg_eq] at hv ⊢
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, nshr_eq] at hv
  simp only [NB.Mem, Nat.sub_eq, Nat.mul_eq, nshr_eq]
  exact ⟨zarg_coord SC L ℓ hL hSC hv.1, zarg_coord TC L ℓ hL hTC hv.2⟩

theorem cexp_v {z : NB} (h : (cexp z).v = true) : z.v = true := by
  obtain ⟨⟨a, b, r, v⟩, hH⟩ : ∃ H, horner z 15 one = H := ⟨_, rfl⟩
  rw [cexp_eq z a b r v hH] at h
  have h15 : (horner z 15 one).v = true := by rw [hH]; exact h
  rw [horner_succ'] at h15
  have h14 := horner_v z 14 _ h15
  rw [hstep_eq] at h14
  exact (cmul_v (cdivn_v (cadd_v h14).2)).1

/-- `epow L SC TC` encloses `n^(−c)` -/
theorem epow_mem {L SC TC n : ℕ} (hn : 0 < n) (hL : |281474976710656 * Real.log n - L| ≤ 1)
    (hSC : SC ≤ 18014398509481984) (hTC : TC ≤ 18014398509481984) (hz : zok L SC TC = true)
    (hv : (epow L SC TC).v = true) : (epow L SC TC).Mem (W n (cof SC TC)) := by
  rw [epow_eq] at hv ⊢
  have hcv : (cexp (zarg L SC TC)).v = true := sqn_v 6 _ hv
  have hzm := zarg_mem hL hSC hTC (cexp_v hcv)
  rw [zok_eq, Nat.ble_eq] at hz
  have hsq := sqn_mem 6 _ _ hv (cexp_mem hcv hzm hz)
  have e : W n (cof SC TC) = Complex.exp ⟨-((SC : ℝ) / 281474976710656 * Real.log n / 64),
      -((TC : ℝ) / 281474976710656 * Real.log n / 64)⟩ ^ (2 ^ 6) := by
    rw [W, ← Complex.exp_nat_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
      ← Complex.natCast_log]
    congr 1
    apply Complex.ext <;>
      simp only [cof, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im] <;> push_cast <;> ring
  rw [e]
  exact hsq

/-- products of enclosed Dirichlet terms -/
theorem cmulW_mem {x y : NB} {m n : ℕ} {z : ℂ} (hx : x.v = true → x.Mem (W m z))
    (hy : y.v = true → y.Mem (W n z)) : (cmul x y).v = true → (cmul x y).Mem (W (m * n) z) := by
  intro hv
  have h := cmul_mem hv (hx (cmul_v hv).1) (hy (cmul_v hv).2)
  rwa [W_mul] at h

theorem nmul_mem {w : NB} {z : ℂ} (hv : (nmul w).v = true) (hw : w.Mem z) :
    (nmul w).Mem (10 * z) := by
  rw [nmul_eq] at hv ⊢
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq] at hv
  obtain ⟨⟨-, h1⟩, h2⟩ := hv
  simp only [NB.Mem, Nat.sub_eq, Nat.mul_eq] at hw ⊢
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  have e1 : ((10 : ℂ) * z).re = 10 * z.re := by simp
  have e2 : ((10 : ℂ) * z).im = 10 * z.im := by simp
  rw [e1, e2]
  push_cast
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨a1, a2⟩ := abs_le.mp hw1
  obtain ⟨b1, b2⟩ := abs_le.mp hw2
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem floor_close (X D : ℕ) (hD : 0 < D) : |(X : ℝ) / D - ((X / D : ℕ) : ℝ)| ≤ 1 := by
  have hb := div_bounds X D hD
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨b1, b2⟩ := hb
  have c1 : ((X / D : ℕ) : ℝ) ≤ (X : ℝ) / D := by rw [le_div_iff₀ hD']; linarith
  have c2 : (X : ℝ) / D ≤ ((X / D : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hD']; linarith
  rw [abs_le]; constructor <;> linarith

/-- `invB SC TC` encloses `1/(1−c)` -/
theorem invB_mem {SC TC : ℕ} (hSC : SC ≤ 281474976710656) (hTC : 0 < TC) :
    (invB SC TC).Mem (1 - cof SC TC)⁻¹ := by
  rw [invB_eq]
  simp only [NB.Mem, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ndiv_eq]
  have hD : 0 < (281474976710656 - SC) * (281474976710656 - SC) + TC * TC :=
    Nat.lt_of_lt_of_le (Nat.mul_pos hTC hTC) (Nat.le_add_left _ _)
  have hT : (0 : ℝ) < TC := by exact_mod_cast hTC
  have hA : ((281474976710656 - SC : ℕ) : ℝ) = 281474976710656 - SC := by
    rw [Nat.cast_sub hSC]; norm_num
  have f1 := floor_close ((281474976710656 - SC) * 79228162514264337593543950336)
    ((281474976710656 - SC) * (281474976710656 - SC) + TC * TC) hD
  have f2 := floor_close (TC * 79228162514264337593543950336)
    ((281474976710656 - SC) * (281474976710656 - SC) + TC * TC) hD
  push_cast [hA] at f1 f2 ⊢
  have eD : Complex.normSq (1 - cof SC TC) * 79228162514264337593543950336 =
      ((281474976710656 - (SC : ℝ)) * (281474976710656 - SC) + TC * TC) := by
    rw [Complex.normSq_apply]
    simp only [cof, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hD' : (0 : ℝ) < (281474976710656 - (SC : ℝ)) * (281474976710656 - SC) + TC * TC := by
    linarith [mul_self_nonneg ((281474976710656 : ℝ) - SC), mul_pos hT hT]
  have hN : (0 : ℝ) < Complex.normSq (1 - cof SC TC) := by linarith
  rw [Complex.inv_re, Complex.inv_im]
  have e1 : 281474976710656 * ((1 - cof SC TC).re / Complex.normSq (1 - cof SC TC)) =
      (281474976710656 - SC) * 79228162514264337593543950336 /
        ((281474976710656 - (SC : ℝ)) * (281474976710656 - SC) + TC * TC) := by
    rw [← eD]
    simp only [cof, Complex.sub_re, Complex.one_re]
    first | (field_simp; done) | (field_simp; ring)
  have e2 : 281474976710656 * (-(1 - cof SC TC).im / Complex.normSq (1 - cof SC TC)) =
      TC * 79228162514264337593543950336 /
        ((281474976710656 - (SC : ℝ)) * (281474976710656 - SC) + TC * TC) := by
    rw [← eD]
    simp only [cof, Complex.sub_im, Complex.one_im]
    first | (field_simp; done) | (field_simp; ring)
  rw [e1, e2]
  constructor
  · have : ∀ u v : ℝ, |u - v| ≤ 1 → |u - (v + 72057594037927936 - 72057594037927936)| ≤ 1 := by
      intro u v h; simpa using h
    exact this _ _ f1
  · have : ∀ u v : ℝ, |u - v| ≤ 1 → |u - (v + 72057594037927936 - 72057594037927936)| ≤ 1 := by
      intro u v h; simpa using h
    exact this _ _ f2

/-- the exact centre ball `⟨O + SC, O + TC, 0⟩` encloses `c` -/
theorem cball_mem (SC TC : ℕ) :
    (⟨Nat.add 72057594037927936 SC, Nat.add 72057594037927936 TC, 0, true⟩ : NB).Mem (cof SC TC) := by
  simp only [NB.Mem, Nat.add_eq, cof]
  push_cast
  constructor <;> (rw [abs_le]; constructor <;> (field_simp; linarith))

/-- `Fof` encloses `A − 10·B/(1−c) − B/2 + c·B/120` -/
theorem Fof_mem {SC TC : ℕ} {F0 wN : NB} {A B : ℂ} (hv : (Fof SC TC F0 wN).v = true)
    (hF : F0.Mem A) (hw : wN.Mem B) (hSC : SC ≤ 281474976710656) (hTC : 0 < TC) :
    (Fof SC TC F0 wN).Mem
      (A - 10 * B * (1 - cof SC TC)⁻¹ - B / ((2 : ℕ) : ℂ) + cof SC TC * B / ((120 : ℕ) : ℂ)) := by
  rw [Fof_eq] at hv ⊢
  have v1 := cadd_v hv
  have v2 := csub_v v1.1
  have v3 := csub_v v2.1
  have hT : (T1of SC TC wN).Mem (10 * B * (1 - cof SC TC)⁻¹) := by
    have hv' := v3.2
    rw [T1of_eq] at hv' ⊢
    exact cmul_mem hv' (nmul_mem (cmul_v hv').1 hw) (invB_mem hSC hTC)
  have m3 := csub_mem v2.1 hF hT
  have m2 := csub_mem v1.1 m3 (cdivn_mem (by norm_num) v2.2 hw)
  have hc := cmul_mem (cdivn_v v1.2) (cball_mem SC TC) hw
  exact cadd_mem hv m2 (cdivn_mem (by norm_num) v1.2 hc)

/-! ## Log certificates: `|2^48·log n − L| ≤ 1`, by exact rational Taylor sums (kernel-checked)

`rh A B j p d` is the exact Horner evaluation, as a fraction, of `Σ_{m<j} q^m/m! + (p/d)·q^j/j!`
with `q = A/B`.  `logOK n L` checks `n ≤ (Σ_{m<22} q₊^m/m!)^4 ≤ exp(4q₊)` with `q₊ = (L+1)/2^50`, and
`exp(4q₋) ≤ (Σ_{m<22} q₋^m/m! + 2^-64)^4 ≤ n` with `q₋ = (L−1)/2^50` (`Real.exp_bound'`, remainder
`≤ 23/(22!·22) < 2^-64`).  P = 48-bit balls cannot do this (the margin is half an ulp). -/

def rh (A B : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, p, d => (p, d)
  | j + 1, p, d =>
    rh A B j (Nat.add (Nat.mul (Nat.mul B d) (j + 1)) (Nat.mul A p)) (Nat.mul (Nat.mul B d) (j + 1))

def logOK (n L : Nat) : Bool :=
  Nat.ble 1 L && Nat.ble L 1125899906842624 &&
  Nat.ble (Nat.mul n (Nat.pow (rh (Nat.add L 1) 1125899906842624 21 1 1).2 4))
    (Nat.pow (rh (Nat.add L 1) 1125899906842624 21 1 1).1 4) &&
  Nat.ble (Nat.pow (Nat.add (Nat.mul (rh (Nat.sub L 1) 1125899906842624 21 1 1).1 18446744073709551616)
      (rh (Nat.sub L 1) 1125899906842624 21 1 1).2) 4)
    (Nat.mul n (Nat.pow (Nat.mul (rh (Nat.sub L 1) 1125899906842624 21 1 1).2 18446744073709551616) 4))

theorem logOK_eq (n L : Nat) : logOK n L =
    (Nat.ble 1 L && Nat.ble L 1125899906842624 &&
    Nat.ble (Nat.mul n (Nat.pow (rh (Nat.add L 1) 1125899906842624 21 1 1).2 4))
      (Nat.pow (rh (Nat.add L 1) 1125899906842624 21 1 1).1 4) &&
    Nat.ble (Nat.pow (Nat.add (Nat.mul (rh (Nat.sub L 1) 1125899906842624 21 1 1).1 18446744073709551616)
        (rh (Nat.sub L 1) 1125899906842624 21 1 1).2) 4)
      (Nat.mul n (Nat.pow (Nat.mul (rh (Nat.sub L 1) 1125899906842624 21 1 1).2 18446744073709551616) 4))) :=
  rfl

theorem rh_zero (A B p d : Nat) : rh A B 0 p d = (p, d) := rfl

theorem rh_succ (A B j p d : Nat) : rh A B (j + 1) p d =
    rh A B j (Nat.add (Nat.mul (Nat.mul B d) (j + 1)) (Nat.mul A p)) (Nat.mul (Nat.mul B d) (j + 1)) := by
  rw [rh]

theorem rh_spec (A B : ℕ) (hB : 0 < B) : ∀ (j p d : ℕ), 0 < d →
    0 < (rh A B j p d).2 ∧ ((rh A B j p d).1 : ℝ) / (rh A B j p d).2 =
      ∑ m ∈ Finset.range j, ((A : ℝ) / B) ^ m / (m.factorial : ℝ) +
        ((p : ℝ) / d) * ((A : ℝ) / B) ^ j / (j.factorial : ℝ) := by
  intro j
  induction j with
  | zero =>
    intro p d hd
    rw [rh_zero]
    exact ⟨hd, by simp⟩
  | succ j ih =>
    intro p d hd
    have hd' : 0 < Nat.mul (Nat.mul B d) (j + 1) := Nat.mul_pos (Nat.mul_pos hB hd) (Nat.succ_pos j)
    obtain ⟨h1, h2⟩ := ih (Nat.add (Nat.mul (Nat.mul B d) (j + 1)) (Nat.mul A p))
      (Nat.mul (Nat.mul B d) (j + 1)) hd'
    rw [rh_succ]
    refine ⟨h1, ?_⟩
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hd'' : (0 : ℝ) < d := by exact_mod_cast hd
    have key : (((Nat.add (Nat.mul (Nat.mul B d) (j + 1)) (Nat.mul A p)) : ℕ) : ℝ) /
        (((Nat.mul (Nat.mul B d) (j + 1)) : ℕ) : ℝ) = 1 + ((A : ℝ) / B) * ((p : ℝ) / d) / ((j : ℝ) + 1) := by
      simp only [Nat.add_eq, Nat.mul_eq]
      push_cast
      field_simp
    rw [h2, key, Finset.sum_range_succ, Nat.factorial_succ]
    generalize (A : ℝ) / B = q
    have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    push_cast
    field_simp
    ring

theorem logOK_sound {n L : ℕ} (hn : 0 < n) (h : logOK n L = true) :
    |281474976710656 * Real.log n - L| ≤ 1 := by
  rw [logOK_eq] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, npow_eq] at h
  obtain ⟨⟨⟨h0, hLB⟩, hup⟩, hlo⟩ := h
  have hB : 0 < 1125899906842624 := by norm_num
  obtain ⟨d1, e1⟩ := rh_spec (L + 1) 1125899906842624 hB 21 1 1 one_pos
  obtain ⟨d2, e2⟩ := rh_spec (L - 1) 1125899906842624 hB 21 1 1 one_pos
  generalize (rh (L + 1) 1125899906842624 21 1 1).1 = P at hup e1
  generalize (rh (L + 1) 1125899906842624 21 1 1).2 = D at hup e1 d1
  generalize (rh (L - 1) 1125899906842624 21 1 1).1 = P' at hlo e2
  generalize (rh (L - 1) 1125899906842624 21 1 1).2 = D' at hlo e2 d2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < D := by exact_mod_cast d1
  have hD' : (0 : ℝ) < D' := by exact_mod_cast d2
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast h0
  have hLB' : (L : ℝ) ≤ 1125899906842624 := by exact_mod_cast hLB
  have cL : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by rw [Nat.cast_sub h0]; norm_num
  push_cast [cL] at e1 e2
  simp only [div_one, one_mul] at e1 e2
  rw [← Finset.sum_range_succ (fun m => (((L : ℝ) + 1) / 1125899906842624) ^ m / (m.factorial : ℝ))]
    at e1
  rw [← Finset.sum_range_succ (fun m => (((L : ℝ) - 1) / 1125899906842624) ^ m / (m.factorial : ℝ))]
    at e2
  -- upper: log n ≤ (L+1)/2^48
  have up1 : (n : ℝ) ≤ ((P : ℝ) / D) ^ 4 := by
    have hc : (n : ℝ) * (D : ℝ) ^ 4 ≤ (P : ℝ) ^ 4 := by exact_mod_cast hup
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact hc
  have up2 : (P : ℝ) / D ≤ Real.exp (((L : ℝ) + 1) / 1125899906842624) := by
    rw [e1]; exact Real.sum_le_exp_of_nonneg (by positivity) 22
  have up3 : (n : ℝ) ≤ Real.exp (((L : ℝ) + 1) / 281474976710656) := by
    have e4 : ((L : ℝ) + 1) / 281474976710656 = ((4 : ℕ) : ℝ) * (((L : ℝ) + 1) / 1125899906842624) := by
      push_cast; ring
    rw [e4, Real.exp_nat_mul]
    exact up1.trans (pow_le_pow_left₀ (by positivity) up2 4)
  have hupper : Real.log n ≤ ((L : ℝ) + 1) / 281474976710656 := (Real.log_le_iff_le_exp hn').mpr up3
  -- lower: (L−1)/2^48 ≤ log n
  have q0 : (0 : ℝ) ≤ ((L : ℝ) - 1) / 1125899906842624 := by
    apply div_nonneg _ (by norm_num); linarith
  have q1 : ((L : ℝ) - 1) / 1125899906842624 ≤ 1 := by
    rw [div_le_one (by norm_num)]; linarith
  have lo1 := Real.exp_bound' q0 q1 (n := 22) (by norm_num)
  have rem : (((L : ℝ) - 1) / 1125899906842624) ^ 22 * ((22 : ℕ) + 1) / ((Nat.factorial 22 : ℕ) * (22 : ℕ)) ≤
      1 / 18446744073709551616 := by
    have hp : (((L : ℝ) - 1) / 1125899906842624) ^ 22 ≤ 1 := pow_le_one₀ q0 q1
    have hfact : ((Nat.factorial 22 : ℕ) : ℝ) = 1124000727777607680000 := by
      rw [show Nat.factorial 22 = 1124000727777607680000 from rfl]; norm_num
    rw [hfact]
    push_cast
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    generalize (((L : ℝ) - 1) / 1125899906842624) ^ 22 = x at hp ⊢
    linarith
  have lo2 : Real.exp (((L : ℝ) - 1) / 1125899906842624) ≤ (P' : ℝ) / D' + 1 / 18446744073709551616 := by
    rw [e2]
    push_cast at lo1
    linarith
  have lo3 : ((P' : ℝ) / D' + 1 / 18446744073709551616) ^ 4 ≤ n := by
    have hc : ((P' : ℝ) * 18446744073709551616 + D') ^ 4 ≤ (n : ℝ) * ((D' : ℝ) * 18446744073709551616) ^ 4 := by
      exact_mod_cast hlo
    have e5 : (P' : ℝ) / D' + 1 / 18446744073709551616 =
        ((P' : ℝ) * 18446744073709551616 + D') / ((D' : ℝ) * 18446744073709551616) := by
      field_simp
    rw [e5, div_pow, div_le_iff₀ (by positivity)]
    exact hc
  have lo4 : Real.exp (((L : ℝ) - 1) / 281474976710656) ≤ n := by
    have e4 : ((L : ℝ) - 1) / 281474976710656 = ((4 : ℕ) : ℝ) * (((L : ℝ) - 1) / 1125899906842624) := by
      push_cast; ring
    rw [e4, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (by positivity) lo2 4).trans lo3
  have hlower : ((L : ℝ) - 1) / 281474976710656 ≤ Real.log n := (Real.le_log_iff_exp_le hn').mpr lo4
  rw [abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hlower (by norm_num : (0 : ℝ) ≤ 281474976710656)
    have e6 : (281474976710656 : ℝ) * (((L : ℝ) - 1) / 281474976710656) = L - 1 := by field_simp
    linarith
  · have := mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 281474976710656)
    have e6 : (281474976710656 : ℝ) * (((L : ℝ) + 1) / 281474976710656) = L + 1 := by field_simp
    linarith

/-! ## The Dirichlet sum over a box: one `term` at a time -/

theorem rmul_v {L : ℕ} {w : NB} (h : (rmul L w).v = true) : w.v = true := by
  rw [rmul_eq] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem zero_mem : (⟨72057594037927936, 72057594037927936, 0, true⟩ : NB).Mem 0 := by
  simp only [NB.Mem, Complex.zero_re, Complex.zero_im]
  norm_num

theorem up_ge' (a d : ℕ) (hd : 0 < d) : (a : ℝ) ≤ (up a d : ℝ) * d := by
  have := up_ge a d hd; linarith

/-- `log n · n^(−z)` -/
noncomputable def LW (n : ℕ) (z : ℂ) : ℂ := (Real.log n : ℂ) * W n z

/-- the order-2 Taylor remainder of one Dirichlet term -/
theorem W_taylor {n : ℕ} (hn : 0 < n) {s c : ℂ} (h1 : ‖s - c‖ * Real.log n ≤ 1) :
    ‖W n s - W n c + (s - c) * LW n c‖ ≤ ‖W n c‖ * (‖s - c‖ * Real.log n) ^ 2 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hℓ : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have eW : ∀ z, W n z = Complex.exp ((Real.log n : ℂ) * (-z)) := by
    intro z; rw [W, Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  have e1 : W n s = W n c * Complex.exp (-((s - c) * (Real.log n : ℂ))) := by
    rw [eW, eW, ← Complex.exp_add]; congr 1; ring
  have hX : ‖-((s - c) * (Real.log n : ℂ))‖ = ‖s - c‖ * Real.log n := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ]
  have e2 : W n s - W n c + (s - c) * LW n c =
      W n c * (Complex.exp (-((s - c) * (Real.log n : ℂ))) - 1 - -((s - c) * (Real.log n : ℂ))) := by
    rw [e1, LW]; ring
  rw [e2, norm_mul, ← hX]
  exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le (by rw [hX]; exact h1))
    (norm_nonneg _)

/-- `2^48·|w|·e² ≤ ⌈M·⌈x²/2^48⌉/2^48⌉` from `2^48·|w| ≤ M`, `2^48·e ≤ x` -/
theorem qterm_bound (M x : ℕ) (wn e : ℝ) (_hwn : 0 ≤ wn) (he : 0 ≤ e) (hM : 281474976710656 * wn ≤ M)
    (hex : 281474976710656 * e ≤ x) :
    281474976710656 * (wn * e ^ 2) ≤
      (up (Nat.mul M (up (Nat.mul x x) 281474976710656)) 281474976710656 : ℝ) := by
  simp only [Nat.mul_eq]
  have hu1 := up_ge' (x * x) 281474976710656 (by norm_num)
  have hu2 := up_ge' (M * up (x * x) 281474976710656) 281474976710656 (by norm_num)
  push_cast at hu1 hu2
  generalize ((up (M * up (x * x) 281474976710656) 281474976710656 : ℕ) : ℝ) = u2 at hu2 ⊢
  generalize ((up (x * x) 281474976710656 : ℕ) : ℝ) = u1 at hu1 hu2
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have k1 : (281474976710656 * wn) * ((281474976710656 * e) * (281474976710656 * e)) ≤ M * (x * x) :=
    mul_le_mul hM (mul_le_mul hex hex (by positivity) hx0) (by positivity) hM0
  have k2 : (M : ℝ) * (x * x) ≤ M * (u1 * 281474976710656) := mul_le_mul_of_nonneg_left hu1 hM0
  have k3 : (M : ℝ) * u1 * 281474976710656 ≤ u2 * 281474976710656 * 281474976710656 :=
    mul_le_mul_of_nonneg_right hu2 (by norm_num)
  have key : 281474976710656 * (wn * e ^ 2) * (281474976710656 * 281474976710656) ≤
      u2 * (281474976710656 * 281474976710656) := by linarith [k1, k2, k3]
  exact le_of_mul_le_mul_right key (by norm_num)

/-- the accumulator invariant: `F` encloses the centre sum, `dS` the centre derivative sum, and `q`
bounds the order-2 Taylor remainder of the sum over the box (each under the matching flag) -/
def TInv (s c : ℂ) (acc : Acc) (Fc Fs dc : ℂ) : Prop :=
  (acc.F.v = true → acc.F.Mem Fc) ∧ (acc.dS.v = true → acc.dS.Mem dc) ∧
  (acc.F.v = true → 281474976710656 * ‖Fs - Fc + (s - c) * dc‖ ≤ (acc.q : ℝ))

theorem TInv_acc0 (s c : ℂ) (ok0 : Bool) : TInv s c (acc0 ok0) 1 1 0 := by
  rw [TInv, acc0_eq]
  refine ⟨fun _ => one_mem, fun _ => zero_mem, fun _ => ?_⟩
  simp

/-- the order-1.5 step: one more Dirichlet term -/
theorem term_sound {s c : ℂ} {rho L n : ℕ} {w : NB} {acc : Acc} {Fc Fs dc : ℂ}
    (hn : 0 < n) (hL : |281474976710656 * Real.log n - L| ≤ 1)
    (hrho : 281474976710656 * ‖s - c‖ ≤ rho)
    (hx : up (Nat.mul rho (Nat.add L 1)) 281474976710656 ≤ 281474976710656)
    (hw : w.v = true → w.Mem (W n c)) (hI : TInv s c acc Fc Fs dc) :
    TInv s c (term rho L w acc) (Fc + W n c) (Fs + W n s) (dc + LW n c) := by
  obtain ⟨hF, hD, hQ⟩ := hI
  rw [TInv, term_eq]
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · exact cadd_mem hv (hF (cadd_v hv).1) (hw (cadd_v hv).2)
  · have hv2 := cadd_v hv
    exact cadd_mem hv (hD hv2.1) (rmul_mem hL hv2.2 (hw (rmul_v hv2.2)))
  · have hv2 := cadd_v hv
    have hwm := hw hv2.2
    have q0 := hQ hv2.1
    have hM := magub_ge hwm
    -- e = ‖s − c‖·log n, with 2^48·e ≤ x ≤ 2^48
    have hℓ : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hℓL : 281474976710656 * Real.log n ≤ (L : ℝ) + 1 := by
      have := (abs_le.mp hL).2; linarith
    have hux := up_ge' (Nat.mul rho (Nat.add L 1)) 281474976710656 (by norm_num)
    have hx' : (up (Nat.mul rho (Nat.add L 1)) 281474976710656 : ℝ) ≤ 281474976710656 := by
      exact_mod_cast hx
    simp only [Nat.mul_eq, Nat.add_eq] at hux hx' ⊢
    push_cast at hux
    generalize hX : up (rho * (L + 1)) 281474976710656 = x at hux hx' ⊢
    have hsc0 : 0 ≤ ‖s - c‖ := norm_nonneg _
    have hex : 281474976710656 * (‖s - c‖ * Real.log n) ≤ x := by
      have k1 : (281474976710656 * ‖s - c‖) * (281474976710656 * Real.log n) ≤ (rho : ℝ) * ((L : ℝ) + 1) :=
        mul_le_mul hrho hℓL (by positivity) (Nat.cast_nonneg _)
      linarith [k1, hux]
    have he1 : ‖s - c‖ * Real.log n ≤ 1 := by linarith [hex, hx']
    have hT := W_taylor hn he1
    have hq := qterm_bound (magub w) x ‖W n c‖ (‖s - c‖ * Real.log n) (norm_nonneg _) (by positivity) hM hex
    have eq : Fs + W n s - (Fc + W n c) + (s - c) * (dc + LW n c) =
        (Fs - Fc + (s - c) * dc) + (W n s - W n c + (s - c) * LW n c) := by ring
    rw [eq]
    have tri := norm_add_le (Fs - Fc + (s - c) * dc) (W n s - W n c + (s - c) * LW n c)
    simp only [Nat.mul_eq] at hq
    push_cast
    linarith [tri, hT, hq, q0]

/-- the centre sum `1 + Σ_{n=2}^{10} n^(−z)` and the derivative sum `Σ log n · n^(−z)` -/
noncomputable def Fsum (z : ℂ) : ℂ :=
  1 + W 2 z + W 3 z + W 4 z + W 5 z + W 6 z + W 7 z + W 8 z + W 9 z + W 10 z
noncomputable def dsum (z : ℂ) : ℂ :=
  0 + LW 2 z + LW 3 z + LW 4 z + LW 5 z + LW 6 z + LW 7 z + LW 8 z + LW 9 z + LW 10 z

theorem cmulW_mem' {x y : NB} {m n k : ℕ} {z : ℂ} (hk : m * n = k) (hx : x.v = true → x.Mem (W m z))
    (hy : y.v = true → y.Mem (W n z)) : (cmul x y).v = true → (cmul x y).Mem (W k z) := by
  rw [← hk]; exact cmulW_mem hx hy

theorem logOK_2 : logOK 2 195103586505167 = true := by decide +kernel
theorem logOK_3 : logOK 3 309231868366897 = true := by decide +kernel
theorem logOK_4 : logOK 4 390207173010335 = true := by decide +kernel
theorem logOK_5 : logOK 5 453016498919635 = true := by decide +kernel
theorem logOK_6 : logOK 6 504335454872064 = true := by decide +kernel
theorem logOK_7 : logOK 7 547725013886373 = true := by decide +kernel
theorem logOK_8 : logOK 8 585310759515502 = true := by decide +kernel
theorem logOK_9 : logOK 9 618463736733793 = true := by decide +kernel
theorem logOK_10 : logOK 10 648120085424803 = true := by decide +kernel

theorem upx_mono (rho L L' : ℕ) (h : L ≤ L') :
    up (Nat.mul rho (Nat.add L 1)) 281474976710656 ≤ up (Nat.mul rho (Nat.add L' 1)) 281474976710656 := by
  unfold up
  simp only [Nat.add_eq, Nat.mul_eq, ndiv_eq]
  exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))) 1

/-- the whole Dirichlet sum over the box, from the kernel-checked flags -/
theorem accOf_sound {s : ℂ} {rho SC TC : ℕ}
    (hrho : 281474976710656 * ‖s - cof SC TC‖ ≤ rho)
    (hSC : SC ≤ 18014398509481984) (hTC : TC ≤ 18014398509481984)
    (hz2 : zok 195103586505167 SC TC = true) (hz3 : zok 309231868366897 SC TC = true)
    (hz5 : zok 453016498919635 SC TC = true) (hz7 : zok 547725013886373 SC TC = true)
    (hx : xNof rho ≤ 281474976710656) :
    TInv s (cof SC TC) (accOf rho SC TC (epow 195103586505167 SC TC) (epow 309231868366897 SC TC)
      (epow 453016498919635 SC TC) (epow 547725013886373 SC TC))
      (Fsum (cof SC TC)) (Fsum s) (dsum (cof SC TC)) := by
  have l2 := logOK_sound (by norm_num) logOK_2
  have l3 := logOK_sound (by norm_num) logOK_3
  have l4 := logOK_sound (by norm_num) logOK_4
  have l5 := logOK_sound (by norm_num) logOK_5
  have l6 := logOK_sound (by norm_num) logOK_6
  have l7 := logOK_sound (by norm_num) logOK_7
  have l8 := logOK_sound (by norm_num) logOK_8
  have l9 := logOK_sound (by norm_num) logOK_9
  have l10 := logOK_sound (by norm_num) logOK_10
  have hx10 : up (Nat.mul rho (Nat.add 648120085424803 1)) 281474976710656 ≤ 281474976710656 := hx
  have hxm : ∀ L, L ≤ 648120085424803 →
      up (Nat.mul rho (Nat.add L 1)) 281474976710656 ≤ 281474976710656 :=
    fun L hL => (upx_mono rho L _ hL).trans hx10
  have w2 : (epow 195103586505167 SC TC).v = true → (epow 195103586505167 SC TC).Mem (W 2 (cof SC TC)) :=
    epow_mem (by norm_num) l2 hSC hTC hz2
  have w3 : (epow 309231868366897 SC TC).v = true → (epow 309231868366897 SC TC).Mem (W 3 (cof SC TC)) :=
    epow_mem (by norm_num) l3 hSC hTC hz3
  have w5 : (epow 453016498919635 SC TC).v = true → (epow 453016498919635 SC TC).Mem (W 5 (cof SC TC)) :=
    epow_mem (by norm_num) l5 hSC hTC hz5
  have w7 : (epow 547725013886373 SC TC).v = true → (epow 547725013886373 SC TC).Mem (W 7 (cof SC TC)) :=
    epow_mem (by norm_num) l7 hSC hTC hz7
  have w4 := cmulW_mem' (k := 4) (by norm_num) w2 w2
  have w6 := cmulW_mem' (k := 6) (by norm_num) w2 w3
  have w8 := cmulW_mem' (k := 8) (by norm_num) w4 w2
  have w9 := cmulW_mem' (k := 9) (by norm_num) w3 w3
  have w10 := cmulW_mem' (k := 10) (by norm_num) w2 w5
  rw [accOf_eq]
  unfold Fsum dsum
  refine term_sound (by norm_num) l10 hrho (hxm _ le_rfl) w10 ?_
  refine term_sound (by norm_num) l9 hrho (hxm _ (by norm_num)) w9 ?_
  refine term_sound (by norm_num) l8 hrho (hxm _ (by norm_num)) w8 ?_
  refine term_sound (by norm_num) l7 hrho (hxm _ (by norm_num)) w7 ?_
  refine term_sound (by norm_num) l6 hrho (hxm _ (by norm_num)) w6 ?_
  refine term_sound (by norm_num) l5 hrho (hxm _ (by norm_num)) w5 ?_
  refine term_sound (by norm_num) l4 hrho (hxm _ (by norm_num)) w4 ?_
  refine term_sound (by norm_num) l3 hrho (hxm _ (by norm_num)) w3 ?_
  refine term_sound (by norm_num) l2 hrho (hxm _ (by norm_num)) w2 ?_
  exact TInv_acc0 _ _ _

/-! ## The EM3 error bound (from the EM3 identity child `ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one`)

`|B₃(y)| = |y³ − 3y²/2 + y/2| ≤ 1/20` on `[0,1]` (the true maximum is √3/36), so with
`∫_10^∞ x^(−σ−3) = 10^(−σ−2)/(σ+2)` and `σ + 2 ≥ 2`:
`‖ζ(s) − F(s)‖ ≤ ‖s‖‖s+1‖‖s+2‖·10^(−σ)/24000`. -/

theorem bF3 (y : ℝ) : bernoulliFun 3 y = y ^ 3 - 3 / 2 * y ^ 2 + 1 / 2 * y := by
  have b3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, by norm_num⟩ (by norm_num)
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ, b3, Nat.choose]
  ring

theorem cubic_lb (a : ℝ) (h1 : -1 / 2 ≤ a) (h2 : a ≤ 1 / 2) : -(1 / 20) ≤ a ^ 3 - a / 4 := by
  rcases le_total 0 a with ha | ha
  · linarith [mul_nonneg (sq_nonneg (a - 29 / 100)) (by linarith : (0 : ℝ) ≤ a + 58 / 100)]
  · linarith [mul_nonneg (mul_nonneg_of_nonpos_of_nonpos ha (by linarith : a - 1 / 2 ≤ 0))
      (by linarith : (0 : ℝ) ≤ a + 1 / 2)]

theorem B3_bound (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) : |bernoulliFun 3 y| ≤ 1 / 20 := by
  rw [bF3, abs_le]
  have e1 := cubic_lb (y - 1 / 2) (by linarith) (by linarith)
  have e2 := cubic_lb (1 / 2 - y) (by linarith) (by linarith)
  constructor <;> linarith [e1, e2]

theorem em3_int_bound (s : ℂ) (hs : 0 < s.re) :
    ‖∫ x in Set.Ioi ((10 : ℕ) : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)‖ ≤
      1 / 20 * (((10 : ℕ) : ℝ) ^ (-s.re - 2) / (s.re + 2)) := by
  have hN : (0 : ℝ) < ((10 : ℕ) : ℝ) := by norm_num
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-s.re - 3)) (Set.Ioi ((10 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN
  have h1 : ‖∫ x in Set.Ioi ((10 : ℕ) : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)‖ ≤
      ∫ x in Set.Ioi ((10 : ℕ) : ℝ), 1 / 20 * x ^ (-s.re - 3) := by
    apply MeasureTheory.norm_integral_le_of_norm_le (hint.const_mul (1 / 20))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hN.trans hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e : (-s - 3).re = -s.re - 3 := by simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (B3_bound _ (Int.fract_nonneg x) (Int.fract_lt_one x).le)
      (Real.rpow_nonneg hx0.le _)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN] at h1
  have e2 : -s.re - 3 + 1 = -(s.re + 2) := by ring
  rw [e2, neg_div_neg_eq] at h1
  have e3 : -s.re - 2 = -(s.re + 2) := by ring
  rw [e3]
  exact h1

/-- the computable part `F(z) = Σ_{n≤10} n^(−z) − 10·10^(−z)/(1−z) − 10^(−z)/2 + z·10^(−z)/120` -/
noncomputable def Fval (z : ℂ) : ℂ :=
  Fsum z - 10 * W 10 z * (1 - z)⁻¹ - W 10 z / ((2 : ℕ) : ℂ) + z * W 10 z / ((120 : ℕ) : ℂ)

theorem em3_bound (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - Fval s‖ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖W 10 s‖ / 24000 := by
  have hz := ZetaEM.riemannZeta_eq_euler_maclaurin_nu_one 10 (by norm_num) s hs hs1
  have hI := em3_int_bound s hs
  generalize (∫ x in Set.Ioi ((10 : ℕ) : ℝ), (bernoulliFun 3 (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - 3)) = I
    at hz hI
  have hne : ((10 : ℕ) : ℂ) ≠ 0 := by norm_num
  have hsum : ∑ n ∈ Finset.Icc (1 : ℕ) 10, ((n : ℕ) : ℂ) ^ (-s) = Fsum s := by
    rw [Finset.sum_Icc_succ_top (b := 9) (by norm_num), Finset.sum_Icc_succ_top (b := 8) (by norm_num),
      Finset.sum_Icc_succ_top (b := 7) (by norm_num), Finset.sum_Icc_succ_top (b := 6) (by norm_num),
      Finset.sum_Icc_succ_top (b := 5) (by norm_num), Finset.sum_Icc_succ_top (b := 4) (by norm_num),
      Finset.sum_Icc_succ_top (b := 3) (by norm_num), Finset.sum_Icc_succ_top (b := 2) (by norm_num),
      Finset.sum_Icc_succ_top (b := 1) (by norm_num), Finset.Icc_self, Finset.sum_singleton]
    simp only [Fsum, W]
    norm_num
  have h1s : ((10 : ℕ) : ℂ) ^ (1 - s) = 10 * W 10 s := by
    rw [W, sub_eq_add_neg, Complex.cpow_add _ _ hne, Complex.cpow_one]
    push_cast; ring
  have h2s : ((10 : ℕ) : ℂ) ^ (-s - 1) = W 10 s / 10 := by
    rw [W, sub_eq_add_neg, Complex.cpow_add _ _ hne, Complex.cpow_neg_one]
    push_cast; ring
  have hW : ((10 : ℕ) : ℂ) ^ (-s) = W 10 s := rfl
  have e : riemannZeta s - Fval s = -(s * (s + 1) * (s + 2) / 6 * I) := by
    rw [hz, hsum, h1s, h2s, hW]
    unfold Fval
    push_cast
    ring
  have hWn : ‖W 10 s‖ = ((10 : ℕ) : ℝ) ^ (-s.re) := by
    rw [W, Complex.norm_natCast_cpow_of_pos (by norm_num), Complex.neg_re]
  have hr : ((10 : ℕ) : ℝ) ^ (-(s.re + 2)) = ((10 : ℕ) : ℝ) ^ (-s.re) / 100 := by
    have h100 : ((10 : ℕ) : ℝ) ^ (-(2 : ℝ)) = 1 / 100 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [neg_add, Real.rpow_add (by norm_num), h100]
    ring
  have e3 : -s.re - 2 = -(s.re + 2) := by ring
  rw [e3, hr] at hI
  rw [e, norm_neg, norm_mul, norm_div, norm_mul, norm_mul, hWn]
  have h6 : ‖(6 : ℂ)‖ = 6 := by norm_num
  rw [h6]
  have hP : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by positivity
  have hX : 0 ≤ ((10 : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (by norm_num) _
  have h2 : ((10 : ℕ) : ℝ) ^ (-s.re) / 100 / (s.re + 2) ≤ ((10 : ℕ) : ℝ) ^ (-s.re) / 100 / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hP6 : 0 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 6 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hI hP6
  have k2 : 1 / 20 * (((10 : ℕ) : ℝ) ^ (-s.re) / 100 / (s.re + 2)) ≤
      1 / 20 * (((10 : ℕ) : ℝ) ^ (-s.re) / 100 / 2) := by linarith [h2]
  have k3 := mul_le_mul_of_nonneg_left k2 hP6
  have e4 : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 6 * (1 / 20 * (((10 : ℕ) : ℝ) ^ (-s.re) / 100 / 2)) =
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ((10 : ℕ) : ℝ) ^ (-s.re) / 24000 := by ring
  linarith [k1, k3, e4]

/-! ## The box test: every Nat bound of `boundT` dominates its analytic term -/

theorem xNof_eq (rho : ℕ) : xNof rho = up (Nat.mul rho 648120085424804) 281474976710656 := rfl
theorem gNof_eq (rho : ℕ) :
    gNof rho = Nat.add (xNof rho) (up (Nat.mul (xNof rho) (xNof rho)) 281474976710656) := rfl
theorem bL1_eq (TC RT rho mN : ℕ) : bL1 TC RT rho mN =
    up (Nat.mul (Nat.mul 10 mN) (Nat.add (gNof rho) (up (Nat.mul rho 281474976710656) TC)))
      (Nat.sub TC RT) := rfl
theorem bL2_eq (rho mN : ℕ) : bL2 rho mN = up (Nat.mul mN (gNof rho)) 562949953421312 := rfl
theorem bL3_eq (SC TC rho mN : ℕ) : bL3 SC TC rho mN =
    up (Nat.add (up (Nat.mul (up (Nat.mul rho mN) 281474976710656) (Nat.add 281474976710656 (gNof rho)))
        281474976710656)
      (up (Nat.mul (up (Nat.mul (Nat.add SC TC) mN) 281474976710656) (gNof rho)) 281474976710656)) 120 :=
  rfl
theorem Uk_eq (tmax sk : ℕ) : Uk tmax sk = Nat.add tmax (up (Nat.mul sk sk) (Nat.mul 2 tmax)) := rfl
theorem bD1_eq (rho : ℕ) (dS : NB) : bD1 rho dS = up (Nat.mul rho (magub dS)) 281474976710656 := rfl
theorem term_ok (rho L : ℕ) (w : NB) (acc : Acc) : (term rho L w acc).ok =
    (acc.ok && Nat.ble (up (Nat.mul rho (Nat.add L 1)) 281474976710656) 281474976710656) := by
  rw [term_eq]
theorem term_w (rho L : ℕ) (w : NB) (acc : Acc) : (term rho L w acc).w = w := by
  rw [term_eq]
theorem acc0_ok (ok0 : Bool) : (acc0 ok0).ok = ok0 := rfl

theorem le_up {a : ℝ} {X d : ℕ} (hd : 0 < d) (h : a * d ≤ X) : a ≤ (up X d : ℝ) := by
  have hu := up_ge X d hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact le_of_mul_le_mul_right (by linarith) hd'

theorem W_shift {n : ℕ} (hn : 0 < n) (s c : ℂ) :
    W n s = W n c * Complex.exp (-((s - c) * (Real.log n : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [W, W, Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add,
    ← Complex.natCast_log]
  congr 1
  ring

theorem srho {s : ℂ} {SC TC RS RT : ℕ} (hs1 : |281474976710656 * s.re - SC| ≤ RS)
    (hs2 : |281474976710656 * s.im - TC| ≤ RT) :
    281474976710656 * ‖s - cof SC TC‖ ≤ ((Nat.add RS RT : ℕ) : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (s - cof SC TC)
  have e1 : (s - cof SC TC).re = (281474976710656 * s.re - SC) / 281474976710656 := by
    simp only [Complex.sub_re, cof]; field_simp
  have e2 : (s - cof SC TC).im = (281474976710656 * s.im - TC) / 281474976710656 := by
    simp only [Complex.sub_im, cof]; field_simp
  rw [e1, e2, abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 281474976710656)] at h
  simp only [Nat.add_eq]
  push_cast
  linarith

theorem Fof_v {SC TC : ℕ} {F0 wN : NB} (h : (Fof SC TC F0 wN).v = true) :
    F0.v = true ∧ wN.v = true := by
  rw [Fof_eq] at h
  have v1 := cadd_v h
  have v2 := csub_v v1.1
  exact ⟨(csub_v v2.1).1, cdivn_v v2.2⟩

theorem fr_le {V r : ℕ} {u : ℝ} (h : |u - ((V : ℝ) - 72057594037927936)| ≤ r) :
    ((dist V - r : ℕ) : ℝ) ≤ |u| := by
  rcases le_total r (dist V) with hr | hr
  · rw [Nat.cast_sub hr, dist_cast]
    have := abs_sub_abs_le_abs_sub ((V : ℝ) - 72057594037927936) u
    rw [abs_sub_comm] at h
    linarith
  · rw [Nat.sub_eq_zero_of_le hr]; simp

/-- the kernel's final test `T² < fr² + fi²` gives `T < 2^48·|F(c)|` -/
theorem center_lower {F : NB} {z : ℂ} {T : ℕ} (hF : F.Mem z)
    (h : T * T < (dist F.a - F.r) * (dist F.a - F.r) + (dist F.b - F.r) * (dist F.b - F.r)) :
    (T : ℝ) < 281474976710656 * ‖z‖ := by
  obtain ⟨h1, h2⟩ := hF
  have a1 := fr_le h1
  have a2 := fr_le h2
  have f0 : (0 : ℝ) ≤ ((dist F.a - F.r : ℕ) : ℝ) := Nat.cast_nonneg _
  have g0 : (0 : ℝ) ≤ ((dist F.b - F.r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc : ((T * T : ℕ) : ℝ) < (((dist F.a - F.r) * (dist F.a - F.r) +
      (dist F.b - F.r) * (dist F.b - F.r) : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul] at hc
  generalize ((dist F.a - F.r : ℕ) : ℝ) = fr at a1 hc f0
  generalize ((dist F.b - F.r : ℕ) : ℝ) = fi at a2 hc g0
  have s1 : fr * fr ≤ (281474976710656 * z.re) ^ 2 := by
    rw [← sq_abs (281474976710656 * z.re), ← pow_two]; exact pow_le_pow_left₀ f0 a1 2
  have s2 : fi * fi ≤ (281474976710656 * z.im) ^ 2 := by
    rw [← sq_abs (281474976710656 * z.im), ← pow_two]; exact pow_le_pow_left₀ g0 a2 2
  have e : (281474976710656 * ‖z‖) ^ 2 =
      (281474976710656 * z.re) ^ 2 + (281474976710656 * z.im) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  by_contra hcon
  rw [not_lt] at hcon
  have := pow_le_pow_left₀ (by positivity) hcon 2
  linarith [this, e, s1, s2, hc]

theorem L10_le : 281474976710656 * Real.log ((10 : ℕ) : ℝ) ≤ 648120085424804 := by
  have := (abs_le.mp (logOK_sound (n := 10) (by norm_num) logOK_10)).2
  have h2 : ((648120085424803 : ℕ) : ℝ) = 648120085424803 := by norm_num
  rw [h2] at this
  linarith

/-- `2^48·‖s − c‖·log 10 ≤ xN` -/
theorem sx_le {s c : ℂ} {rho : ℕ} (hrho : 281474976710656 * ‖s - c‖ ≤ rho) :
    281474976710656 * (‖s - c‖ * Real.log ((10 : ℕ) : ℝ)) ≤ (xNof rho : ℝ) := by
  have hℓ : 0 ≤ Real.log ((10 : ℕ) : ℝ) := Real.log_natCast_nonneg 10
  have hux := up_ge' (Nat.mul rho 648120085424804) 281474976710656 (by norm_num)
  rw [← xNof_eq] at hux
  simp only [Nat.mul_eq] at hux
  push_cast at hux
  have k1 : (281474976710656 * ‖s - c‖) * (281474976710656 * Real.log ((10 : ℕ) : ℝ)) ≤
      (rho : ℝ) * 648120085424804 :=
    mul_le_mul hrho L10_le (by positivity) (Nat.cast_nonneg _)
  have key : 281474976710656 * (‖s - c‖ * Real.log ((10 : ℕ) : ℝ)) * 281474976710656 ≤
      (xNof rho : ℝ) * 281474976710656 := by linarith [k1, hux]
  exact le_of_mul_le_mul_right key (by norm_num)

/-- `2^48·|10^(−s) − 10^(−c)| ≤ |10^(−c)|·gN` -/
theorem Wdiff {s c : ℂ} {rho : ℕ} (hrho : 281474976710656 * ‖s - c‖ ≤ rho)
    (hxN : xNof rho ≤ 281474976710656) :
    281474976710656 * ‖W 10 s - W 10 c‖ ≤ ‖W 10 c‖ * (gNof rho : ℝ) := by
  have hℓ : 0 ≤ Real.log ((10 : ℕ) : ℝ) := Real.log_natCast_nonneg 10
  have hex := sx_le hrho
  have hx' : (xNof rho : ℝ) ≤ 281474976710656 := by exact_mod_cast hxN
  generalize he : ‖s - c‖ * Real.log ((10 : ℕ) : ℝ) = e at hex
  have he0 : 0 ≤ e := by rw [← he]; positivity
  have he1 : e ≤ 1 := by linarith
  have hX : ‖-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))‖ = e := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ, he]
  have hE1 := Complex.norm_exp_sub_one_sub_id_le (x := -((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ)))
    (by rw [hX]; exact he1)
  rw [hX] at hE1
  have hE : ‖Complex.exp (-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))) - 1‖ ≤ e + e ^ 2 := by
    have t := norm_sub_le (Complex.exp (-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))) - 1 -
      -((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))) (-(-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, hX] at t
    linarith
  have hg : 281474976710656 * (e + e ^ 2) ≤ (gNof rho : ℝ) := by
    rw [gNof_eq]
    simp only [Nat.add_eq]
    push_cast
    have hu : 281474976710656 * e ^ 2 ≤ (up (Nat.mul (xNof rho) (xNof rho)) 281474976710656 : ℝ) := by
      apply le_up (by norm_num)
      simp only [Nat.mul_eq]
      push_cast
      have hxN0 : (0 : ℝ) ≤ (xNof rho : ℝ) := Nat.cast_nonneg _
      linarith [mul_le_mul hex hex (by positivity) hxN0]
    linarith
  rw [W_shift (by norm_num) s c]
  have eq : W 10 c * Complex.exp (-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))) - W 10 c =
      W 10 c * (Complex.exp (-((s - c) * (Real.log ((10 : ℕ) : ℝ) : ℂ))) - 1) := by ring
  rw [eq, norm_mul]
  have hw0 : 0 ≤ ‖W 10 c‖ := norm_nonneg _
  have k := mul_le_mul_of_nonneg_left hE hw0
  linarith [k, mul_le_mul_of_nonneg_left hg hw0]

/-- `2^48·|10^(−s)| ≤ nsm` (only the real offset `RS` matters) -/
theorem Wnorm_s {s : ℂ} {SC TC RS mN : ℕ} (hs1 : |281474976710656 * s.re - SC| ≤ RS)
    (hxs : up (Nat.mul RS 648120085424804) 281474976710656 ≤ 281474976710656)
    (hwc : 281474976710656 * ‖W 10 (cof SC TC)‖ ≤ mN) :
    281474976710656 * ‖W 10 s‖ ≤ (nsmOf RS mN : ℝ) := by
  have hℓ : 0 ≤ Real.log ((10 : ℕ) : ℝ) := Real.log_natCast_nonneg 10
  rw [W_shift (by norm_num) s (cof SC TC), norm_mul, Complex.norm_exp]
  have hre : (-((s - cof SC TC) * (Real.log ((10 : ℕ) : ℝ) : ℂ))).re =
      -((s.re - (SC : ℝ) / 281474976710656) * Real.log ((10 : ℕ) : ℝ)) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, cof]
    ring
  rw [hre]
  -- y = xs/2^48 bounds the exponent
  have hux := up_ge' (Nat.mul RS 648120085424804) 281474976710656 (by norm_num)
  have hxs' : (up (Nat.mul RS 648120085424804) 281474976710656 : ℝ) ≤ 281474976710656 := by
    exact_mod_cast hxs
  simp only [Nat.mul_eq] at hux hxs'
  push_cast at hux
  generalize hxsd : up (RS * 648120085424804) 281474976710656 = xs at hux hxs'
  have hd : |s.re - (SC : ℝ) / 281474976710656| * 281474976710656 ≤ RS := by
    have e : (281474976710656 : ℝ) * s.re - SC = (s.re - (SC : ℝ) / 281474976710656) * 281474976710656 := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 281474976710656)] at hs1
    exact hs1
  have hy : -((s.re - (SC : ℝ) / 281474976710656) * Real.log ((10 : ℕ) : ℝ)) ≤ (xs : ℝ) / 281474976710656 := by
    have k2 : |s.re - (SC : ℝ) / 281474976710656| * 281474976710656 *
        (281474976710656 * Real.log ((10 : ℕ) : ℝ)) ≤ (RS : ℝ) * 648120085424804 :=
      mul_le_mul hd L10_le (by positivity) (Nat.cast_nonneg _)
    have k3 : -(s.re - (SC : ℝ) / 281474976710656) * Real.log ((10 : ℕ) : ℝ) ≤
        |s.re - (SC : ℝ) / 281474976710656| * Real.log ((10 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hℓ
    rw [le_div_iff₀ (by norm_num)]
    linarith [k3, k2, hux]
  have hy1 : (xs : ℝ) / 281474976710656 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hxs'
  have hy0 : 0 ≤ (xs : ℝ) / 281474976710656 := by positivity
  have hexp : Real.exp (-((s.re - (SC : ℝ) / 281474976710656) * Real.log ((10 : ℕ) : ℝ))) ≤
      1 + (xs : ℝ) / 281474976710656 + ((xs : ℝ) / 281474976710656) ^ 2 := by
    have t := Real.abs_exp_sub_one_sub_id_le (x := (xs : ℝ) / 281474976710656) (by rw [abs_of_nonneg hy0]; exact hy1)
    have t2 := Real.exp_le_exp.mpr hy
    have t3 := (abs_le.mp t).2
    linarith
  rw [nsmOf_eq]
  simp only [Nat.mul_eq, Nat.add_eq]
  rw [hxsd]
  apply le_up (by norm_num)
  have hu2 := up_ge' (xs * xs) 281474976710656 (by norm_num)
  push_cast at hu2 ⊢
  have hw0 : 0 ≤ ‖W 10 (cof SC TC)‖ := norm_nonneg _
  have hm0 : (0 : ℝ) ≤ mN := Nat.cast_nonneg _
  have hxs0 : (0 : ℝ) ≤ xs := Nat.cast_nonneg _
  have k := mul_le_mul_of_nonneg_left hexp hw0
  have p1 : 281474976710656 * ‖W 10 (cof SC TC)‖ *
      (281474976710656 + (xs : ℝ) + (xs : ℝ) ^ 2 / 281474976710656) ≤
      mN * (281474976710656 + (xs : ℝ) + (xs : ℝ) ^ 2 / 281474976710656) :=
    mul_le_mul_of_nonneg_right hwc (by positivity)
  have hq : (xs : ℝ) ^ 2 / 281474976710656 ≤ (up (xs * xs) 281474976710656 : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]; linarith [hu2]
  have p2 : (mN : ℝ) * (281474976710656 + (xs : ℝ) + (xs : ℝ) ^ 2 / 281474976710656) ≤
      mN * (281474976710656 + xs + (up (xs * xs) 281474976710656 : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hm0
  have p3 := mul_le_mul_of_nonneg_left k (by norm_num : (0 : ℝ) ≤ 281474976710656 * 281474976710656)
  have e : 281474976710656 * 281474976710656 *
      (‖W 10 (cof SC TC)‖ * (1 + (xs : ℝ) / 281474976710656 + ((xs : ℝ) / 281474976710656) ^ 2)) =
      281474976710656 * ‖W 10 (cof SC TC)‖ *
        (281474976710656 + (xs : ℝ) + (xs : ℝ) ^ 2 / 281474976710656) := by ring
  rw [e] at p3
  linarith [p1, p2, p3]

/-- `2^48·‖z + k‖ ≤ Uk` for `0 ≤ 2^48·(Re z + k) ≤ sk`, `0 < 2^48·Im z ≤ tmax` -/
theorem Uk_bound {z : ℂ} {tmax sk : ℕ} (k : ℝ) (htp : 0 < tmax)
    (h1 : 0 ≤ 281474976710656 * (z.re + k)) (h2 : 281474976710656 * (z.re + k) ≤ sk)
    (h3 : 0 ≤ 281474976710656 * z.im) (h4 : 281474976710656 * z.im ≤ tmax) :
    281474976710656 * ‖z + k‖ ≤ (Uk tmax sk : ℝ) := by
  rw [Uk_eq]
  simp only [Nat.add_eq]
  have hu := up_ge' (Nat.mul sk sk) (Nat.mul 2 tmax) (by simp only [Nat.mul_eq]; omega)
  simp only [Nat.mul_eq] at hu ⊢
  push_cast at hu ⊢
  have hu0' : (0 : ℝ) ≤ ((up (sk * sk) (2 * tmax) : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((up (sk * sk) (2 * tmax) : ℕ) : ℝ) = u at hu hu0' ⊢
  have ht0 : (0 : ℝ) < tmax := by exact_mod_cast htp
  have hu0 : 0 ≤ u := hu0'
  have e : (281474976710656 * ‖z + k‖) ^ 2 =
      (281474976710656 * (z.re + k)) ^ 2 + (281474976710656 * z.im) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    ring
  have s1 : (281474976710656 * (z.re + k)) ^ 2 ≤ (sk : ℝ) ^ 2 := pow_le_pow_left₀ h1 h2 2
  have s2 : (281474976710656 * z.im) ^ 2 ≤ (tmax : ℝ) ^ 2 := pow_le_pow_left₀ h3 h4 2
  have hsq : (281474976710656 * ‖z + k‖) ^ 2 ≤ ((tmax : ℝ) + u) ^ 2 := by
    linarith [e, s1, s2, hu, sq_nonneg u]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-! ## The five Lipschitz/EM3 bounds of `boundT`, the box theorem and the quadtree theorem

Each bound is a pure-real `*_core` lemma (all quantities are variables, `S = 2^48` included, so the
arithmetic stays small), instantiated by a `*_sound` lemma that reads the Nat bound. -/

theorem L1_core (S Tm TC δ wc a b e mN gN rho u : ℝ) (hS : 0 < S) (hTm : 0 < Tm) (hTC : 0 < TC)
    (hδ0 : 0 ≤ δ) (hwc0 : 0 ≤ wc) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e) (hmN : 0 ≤ mN)
    (hgN : 0 ≤ gN) (hrho0 : 0 ≤ rho) (hδ : S * δ ≤ wc * gN) (hwc : S * wc ≤ mN) (hA : Tm * a ≤ S)
    (hB : TC * b ≤ S) (hrho : S * e ≤ rho) (hu : rho * S ≤ u * TC) :
    S * (10 * (δ * a + wc * (a * e * b))) * Tm ≤ 10 * mN * (gN + u) := by
  have m1 : (S * wc) * (Tm * a) ≤ mN * S := mul_le_mul hwc hA (by positivity) hmN
  have m2 : (S * e) * (TC * b) ≤ rho * S := mul_le_mul hrho hB (by positivity) hrho0
  have m3 : ((S * wc) * (Tm * a)) * ((S * e) * (TC * b)) ≤ (mN * S) * (rho * S) :=
    mul_le_mul m1 m2 (by positivity) (by positivity)
  have m4 : (mN * S) * (rho * S) ≤ (mN * S) * (u * TC) := mul_le_mul_of_nonneg_left hu (by positivity)
  have X2 : S * (10 * (wc * (a * e * b))) * Tm * (TC * S) ≤ 10 * mN * u * (TC * S) := by
    linarith [m3, m4]
  have X2' := le_of_mul_le_mul_right X2 (by positivity)
  have n1 : (S * δ) * (Tm * a) ≤ (wc * gN) * S := mul_le_mul hδ hA (by positivity) (by positivity)
  have n2 : (S * wc) * gN ≤ mN * gN := mul_le_mul_of_nonneg_right hwc hgN
  have X1 : S * (10 * (δ * a)) * Tm ≤ 10 * mN * gN := by linarith [n1, n2]
  linarith [X1, X2']

theorem one_sub_ne {z : ℂ} {t : ℝ} (hz : t ≤ z.im) : t ≤ ‖1 - z‖ := by
  have := Complex.abs_im_le_norm (1 - z)
  rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
  linarith [le_abs_self z.im]

theorem L1_sound {s : ℂ} {SC TC RT rho mN : ℕ} (hRT : RT < TC)
    (hsi : (TC : ℝ) - RT ≤ 281474976710656 * s.im)
    (hrho : 281474976710656 * ‖s - cof SC TC‖ ≤ rho)
    (hwc : 281474976710656 * ‖W 10 (cof SC TC)‖ ≤ mN)
    (hδ : 281474976710656 * ‖W 10 s - W 10 (cof SC TC)‖ ≤ ‖W 10 (cof SC TC)‖ * (gNof rho : ℝ)) :
    281474976710656 * ‖10 * W 10 s * (1 - s)⁻¹ - 10 * W 10 (cof SC TC) * (1 - cof SC TC)⁻¹‖ ≤
      (bL1 TC RT rho mN : ℝ) := by
  have hRT' : (RT : ℝ) < TC := by exact_mod_cast hRT
  have hTm : (0 : ℝ) < (TC : ℝ) - RT := by linarith
  have hTC : (0 : ℝ) < TC := by linarith [(Nat.cast_nonneg RT : (0 : ℝ) ≤ RT)]
  have hS : (0 : ℝ) < 281474976710656 := by norm_num
  have hs1 := one_sub_ne (z := s) (t := ((TC : ℝ) - RT) / 281474976710656)
    (by rw [div_le_iff₀ hS]; linarith)
  have hc1 := one_sub_ne (z := cof SC TC) (t := (TC : ℝ) / 281474976710656) (by simp [cof])
  have hn1 : (0 : ℝ) < ‖1 - s‖ := lt_of_lt_of_le (div_pos hTm hS) hs1
  have hn2 : (0 : ℝ) < ‖1 - cof SC TC‖ := lt_of_lt_of_le (div_pos hTC hS) hc1
  have hne1 : (1 : ℂ) - s ≠ 0 := norm_pos_iff.mp hn1
  have hne2 : (1 : ℂ) - cof SC TC ≠ 0 := norm_pos_iff.mp hn2
  have hA : ((TC : ℝ) - RT) * ‖(1 - s)⁻¹‖ ≤ 281474976710656 := by
    rw [norm_inv, ← div_eq_mul_inv, div_le_iff₀ hn1]
    rw [div_le_iff₀ hS] at hs1; linarith
  have hB : (TC : ℝ) * ‖(1 - cof SC TC)⁻¹‖ ≤ 281474976710656 := by
    rw [norm_inv, ← div_eq_mul_inv, div_le_iff₀ hn2]
    rw [div_le_iff₀ hS] at hc1; linarith
  have eq : 10 * W 10 s * (1 - s)⁻¹ - 10 * W 10 (cof SC TC) * (1 - cof SC TC)⁻¹ =
      10 * ((W 10 s - W 10 (cof SC TC)) * (1 - s)⁻¹ +
        W 10 (cof SC TC) * ((1 - s)⁻¹ * (s - cof SC TC) * (1 - cof SC TC)⁻¹)) := by
    have hi : (1 - s)⁻¹ * (s - cof SC TC) * (1 - cof SC TC)⁻¹ = (1 - s)⁻¹ - (1 - cof SC TC)⁻¹ := by
      rw [inv_sub_inv' hne1 hne2]; ring
    rw [hi]; ring
  rw [eq, norm_mul, Complex.norm_ofNat]
  have tri := norm_add_le ((W 10 s - W 10 (cof SC TC)) * (1 - s)⁻¹)
    (W 10 (cof SC TC) * ((1 - s)⁻¹ * (s - cof SC TC) * (1 - cof SC TC)⁻¹))
  simp only [norm_mul] at tri
  rw [bL1_eq]
  apply le_up (Nat.sub_pos_of_lt hRT)
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  rw [Nat.cast_sub hRT.le]
  have hu := up_ge' (rho * 281474976710656) TC (by omega)
  push_cast at hu ⊢
  have core := L1_core 281474976710656 ((TC : ℝ) - RT) TC ‖W 10 s - W 10 (cof SC TC)‖
    ‖W 10 (cof SC TC)‖ ‖(1 - s)⁻¹‖ ‖(1 - cof SC TC)⁻¹‖ ‖s - cof SC TC‖ mN (gNof rho) rho
    (up (rho * 281474976710656) TC) hS hTm hTC (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hδ hwc hA hB hrho hu
  have k := mul_le_mul_of_nonneg_left tri
    (by positivity : (0 : ℝ) ≤ 281474976710656 * 10 * ((TC : ℝ) - RT))
  linarith [core, k]

theorem L2_sound {s c : ℂ} {rho mN : ℕ} (hwc : 281474976710656 * ‖W 10 c‖ ≤ mN)
    (hδ : 281474976710656 * ‖W 10 s - W 10 c‖ ≤ ‖W 10 c‖ * (gNof rho : ℝ)) :
    281474976710656 * ‖(W 10 s - W 10 c) / ((2 : ℕ) : ℂ)‖ ≤ (bL2 rho mN : ℝ) := by
  rw [bL2_eq]
  apply le_up (by norm_num)
  rw [norm_div, Complex.norm_natCast]
  simp only [Nat.mul_eq]
  push_cast
  have hg : (0 : ℝ) ≤ gNof rho := Nat.cast_nonneg _
  have k := mul_le_mul_of_nonneg_right hwc hg
  have e : 281474976710656 * (‖W 10 s - W 10 c‖ / 2) * 562949953421312 =
      281474976710656 * (281474976710656 * ‖W 10 s - W 10 c‖) := by ring
  rw [e]
  linarith [k, hδ]

theorem L3_core (S δ wc ws e cn mN gN rho sct v1 v2 : ℝ) (hS : 0 < S) (hδ0 : 0 ≤ δ) (hwc0 : 0 ≤ wc)
    (hws0 : 0 ≤ ws) (he0 : 0 ≤ e) (hcn0 : 0 ≤ cn) (hmN : 0 ≤ mN) (hgN : 0 ≤ gN) (hrho0 : 0 ≤ rho)
    (hδ : S * δ ≤ wc * gN) (hwc : S * wc ≤ mN) (hws : ws ≤ wc + δ) (hrho : S * e ≤ rho)
    (hcn : S * cn ≤ sct) (hv1 : rho * mN ≤ v1 * S) (hv2 : sct * mN ≤ v2 * S) :
    S * (e * ws + cn * δ) * S ≤ v1 * (S + gN) + v2 * gN := by
  -- (S e ws) S ≤ v1 (S + gN)
  have a1 : (S * ws) * S ≤ (mN * S) + mN * gN := by
    have t1 : S * ws * S ≤ S * (wc + δ) * S := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hws hS.le) hS.le
    have t2 : S * wc * gN ≤ mN * gN := mul_le_mul_of_nonneg_right hwc hgN
    linarith [t1, t2, mul_le_mul_of_nonneg_right hwc hS.le, mul_le_mul_of_nonneg_right hδ hS.le]
  have a2 : (S * e) * ((S * ws) * S) ≤ rho * ((mN * S) + mN * gN) :=
    mul_le_mul hrho a1 (by positivity) hrho0
  have a3 : rho * ((mN * S) + mN * gN) ≤ v1 * S * (S + gN) := by
    have := mul_le_mul_of_nonneg_right hv1 (by positivity : (0 : ℝ) ≤ S + gN)
    linarith [this]
  have b1 : (S * cn) * ((S * δ) * S) ≤ sct * (wc * gN * S) :=
    mul_le_mul hcn (mul_le_mul_of_nonneg_right hδ hS.le) (by positivity) (le_trans (by positivity) hcn)
  have b2 : sct * (wc * gN * S) ≤ sct * mN * gN := by
    have := mul_le_mul_of_nonneg_right hwc hgN
    have hsct : 0 ≤ sct := le_trans (by positivity) hcn
    linarith [mul_le_mul_of_nonneg_left this hsct]
  have b3 : sct * mN * gN ≤ v2 * S * gN := mul_le_mul_of_nonneg_right hv2 hgN
  have key : S * (e * ws + cn * δ) * S * S ≤ (v1 * (S + gN) + v2 * gN) * S := by
    linarith [a2, a3, b1, b2, b3]
  exact le_of_mul_le_mul_right key hS

theorem L3_sound {s : ℂ} {SC TC rho mN : ℕ}
    (hrho : 281474976710656 * ‖s - cof SC TC‖ ≤ rho)
    (hwc : 281474976710656 * ‖W 10 (cof SC TC)‖ ≤ mN)
    (hδ : 281474976710656 * ‖W 10 s - W 10 (cof SC TC)‖ ≤ ‖W 10 (cof SC TC)‖ * (gNof rho : ℝ)) :
    281474976710656 * ‖(s * W 10 s - cof SC TC * W 10 (cof SC TC)) / ((120 : ℕ) : ℂ)‖ ≤
      (bL3 SC TC rho mN : ℝ) := by
  have hS : (0 : ℝ) < 281474976710656 := by norm_num
  have eq : s * W 10 s - cof SC TC * W 10 (cof SC TC) =
      (s - cof SC TC) * W 10 s + cof SC TC * (W 10 s - W 10 (cof SC TC)) := by ring
  have tri := norm_add_le ((s - cof SC TC) * W 10 s) (cof SC TC * (W 10 s - W 10 (cof SC TC)))
  rw [← eq, norm_mul, norm_mul] at tri
  have hws : ‖W 10 s‖ ≤ ‖W 10 (cof SC TC)‖ + ‖W 10 s - W 10 (cof SC TC)‖ := by
    have := norm_add_le (W 10 (cof SC TC)) (W 10 s - W 10 (cof SC TC))
    rwa [add_sub_cancel] at this
  have hcn : 281474976710656 * ‖cof SC TC‖ ≤ ((SC + TC : ℕ) : ℝ) := by
    have := Complex.norm_le_abs_re_add_abs_im (cof SC TC)
    have hre : (cof SC TC).re = (SC : ℝ) / 281474976710656 := rfl
    have him : (cof SC TC).im = (TC : ℝ) / 281474976710656 := rfl
    rw [hre, him, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at this
    push_cast
    have e2 : (281474976710656 : ℝ) * ((SC : ℝ) / 281474976710656 + (TC : ℝ) / 281474976710656) =
        SC + TC := by field_simp
    linarith [this, e2]
  have hv1 := up_ge' (rho * mN) 281474976710656 (by norm_num)
  have hv2 := up_ge' ((SC + TC) * mN) 281474976710656 (by norm_num)
  push_cast at hv1 hv2
  have core := L3_core 281474976710656 ‖W 10 s - W 10 (cof SC TC)‖ ‖W 10 (cof SC TC)‖ ‖W 10 s‖
    ‖s - cof SC TC‖ ‖cof SC TC‖ mN (gNof rho) rho ((SC : ℝ) + TC) (up (rho * mN) 281474976710656)
    (up ((SC + TC) * mN) 281474976710656) hS (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hδ hwc hws hrho (by push_cast at hcn; exact hcn) hv1 hv2
  rw [bL3_eq, norm_div, Complex.norm_natCast]
  apply le_up (by norm_num)
  simp only [Nat.mul_eq, Nat.add_eq]
  have hw1 := up_ge' (up (rho * mN) 281474976710656 * (281474976710656 + gNof rho)) 281474976710656
    (by norm_num)
  have hw2 := up_ge' (up ((SC + TC) * mN) 281474976710656 * gNof rho) 281474976710656 (by norm_num)
  push_cast at hw1 hw2 ⊢
  generalize ((up (up (rho * mN) 281474976710656 * (281474976710656 + gNof rho)) 281474976710656 : ℕ) : ℝ)
    = A1 at hw1 ⊢
  generalize ((up (up ((SC + TC) * mN) 281474976710656 * gNof rho) 281474976710656 : ℕ) : ℝ) = A2 at hw2 ⊢
  have c2 : 281474976710656 * (‖s - cof SC TC‖ * ‖W 10 s‖ + ‖cof SC TC‖ * ‖W 10 s - W 10 (cof SC TC)‖) *
      281474976710656 ≤ (A1 + A2) * 281474976710656 := by linarith [core, hw1, hw2]
  have c3 := le_of_mul_le_mul_right c2 hS
  have k := mul_le_mul_of_nonneg_left tri hS.le
  have e3 : 281474976710656 * (‖s * W 10 s - cof SC TC * W 10 (cof SC TC)‖ / 120) * 120 =
      281474976710656 * ‖s * W 10 s - cof SC TC * W 10 (cof SC TC)‖ := by ring
  rw [e3]
  linarith [k, c3]

theorem D1_sound {s c d : ℂ} {rho : ℕ} {dS : NB} (hrho : 281474976710656 * ‖s - c‖ ≤ rho)
    (hd : dS.Mem d) : 281474976710656 * ‖(s - c) * d‖ ≤ (bD1 rho dS : ℝ) := by
  rw [bD1_eq]
  apply le_up (by norm_num)
  simp only [Nat.mul_eq]
  push_cast
  have hm := magub_ge hd
  rw [norm_mul]
  have k := mul_le_mul hrho hm (by positivity) (Nat.cast_nonneg _)
  linarith [k]

theorem E_core (S p0 p1 p2 ws U0 U1 U2 nsm v1 v2 v3 : ℝ) (hS : 0 < S) (h0 : 0 ≤ p0) (h1 : 0 ≤ p1)
    (h2 : 0 ≤ p2) (hw : 0 ≤ ws) (u0 : S * p0 ≤ U0) (u1 : S * p1 ≤ U1) (u2 : S * p2 ≤ U2)
    (hn : S * ws ≤ nsm) (hv1 : U0 * U1 ≤ v1 * S) (hv2 : v1 * U2 ≤ v2 * S) (hv3 : v2 * nsm ≤ v3 * S) :
    S * (p0 * p1 * p2 * ws) ≤ v3 := by
  have k1 : S * p0 * p1 ≤ v1 := by
    have := mul_le_mul u0 u1 (by positivity) (le_trans (by positivity) u0)
    exact le_of_mul_le_mul_right (by linarith) hS
  have k2 : S * p0 * p1 * p2 ≤ v2 := by
    have := mul_le_mul k1 u2 (by positivity) (le_trans (by positivity) k1)
    exact le_of_mul_le_mul_right (by linarith) hS
  have k3 : S * p0 * p1 * p2 * ws ≤ v3 := by
    have := mul_le_mul k2 hn (by positivity) (le_trans (by positivity) k2)
    exact le_of_mul_le_mul_right (by linarith) hS
  linarith

theorem E_sound {s : ℂ} {SC TC RS RT mN : ℕ} (hs1 : |281474976710656 * s.re - SC| ≤ RS)
    (hs2 : |281474976710656 * s.im - TC| ≤ RT) (hσ : 0 < s.re) (hRT : RT < TC)
    (hxs : up (Nat.mul RS 648120085424804) 281474976710656 ≤ 281474976710656)
    (hwc : 281474976710656 * ‖W 10 (cof SC TC)‖ ≤ mN) :
    281474976710656 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖W 10 s‖ / 24000) ≤ (bE SC TC RS RT mN : ℝ) := by
  have hS : (0 : ℝ) < 281474976710656 := by norm_num
  have hn := Wnorm_s hs1 hxs hwc
  obtain ⟨a1, a2⟩ := abs_le.mp hs1
  obtain ⟨b1, b2⟩ := abs_le.mp hs2
  have hRT' : (RT : ℝ) < TC := by exact_mod_cast hRT
  have htp : 0 < Nat.add TC RT := by simp only [Nat.add_eq]; omega
  have him0 : 0 ≤ 281474976710656 * s.im := by linarith
  have himT : 281474976710656 * s.im ≤ ((Nat.add TC RT : ℕ) : ℝ) := by
    simp only [Nat.add_eq]; push_cast; linarith
  have u0 := Uk_bound (z := s) (tmax := Nat.add TC RT) (sk := Nat.add SC RS) 0 htp
    (by linarith) (by simp only [Nat.add_eq]; push_cast; linarith) him0 himT
  have u1 := Uk_bound (z := s) (tmax := Nat.add TC RT) (sk := Nat.add (Nat.add SC RS) 281474976710656) 1
    htp (by linarith) (by simp only [Nat.add_eq]; push_cast; linarith) him0 himT
  have u2 := Uk_bound (z := s) (tmax := Nat.add TC RT) (sk := Nat.add (Nat.add SC RS) 562949953421312) 2
    htp (by linarith) (by simp only [Nat.add_eq]; push_cast; linarith) him0 himT
  rw [Complex.ofReal_zero, add_zero] at u0
  rw [Complex.ofReal_one] at u1
  rw [Complex.ofReal_ofNat] at u2
  rw [bE_eq]
  apply le_up (by norm_num)
  simp only [Nat.mul_eq]
  have hv1 := up_ge' (Uk (Nat.add TC RT) (Nat.add SC RS) * Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 281474976710656))
    281474976710656 (by norm_num)
  have hv2 := up_ge' (up (Uk (Nat.add TC RT) (Nat.add SC RS) *
      Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 281474976710656)) 281474976710656 *
      Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 562949953421312)) 281474976710656 (by norm_num)
  have hv3 := up_ge' (up (up (Uk (Nat.add TC RT) (Nat.add SC RS) *
      Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 281474976710656)) 281474976710656 *
      Uk (Nat.add TC RT) (Nat.add (Nat.add SC RS) 562949953421312)) 281474976710656 * nsmOf RS mN)
      281474976710656 (by norm_num)
  push_cast at hv1 hv2 hv3 ⊢
  have core := E_core 281474976710656 ‖s‖ ‖s + 1‖ ‖s + 2‖ ‖W 10 s‖ _ _ _ _ _ _ _ hS (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) u0 u1 u2 hn hv1 hv2 hv3
  have e : 281474976710656 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖W 10 s‖ / 24000) * 24000 =
      281474976710656 * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖W 10 s‖) := by ring
  rw [e]
  exact core

theorem accOf_ok {rho SC TC : ℕ} {w2 w3 w5 w7 : NB} (h : (accOf rho SC TC w2 w3 w5 w7).ok = true) :
    zok 195103586505167 SC TC = true ∧ zok 309231868366897 SC TC = true ∧
    zok 453016498919635 SC TC = true ∧ zok 547725013886373 SC TC = true := by
  rw [accOf_eq] at h
  simp only [term_ok, acc0_ok, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.2⟩

theorem accOf_w (rho SC TC : ℕ) (w2 w3 w5 w7 : NB) : (accOf rho SC TC w2 w3 w5 w7).w = cmul w2 w5 := by
  rw [accOf_eq, term_w]

theorem up_mono (a b d : ℕ) (h : a ≤ b) : up a d ≤ up b d := by
  unfold up
  simp only [Nat.add_eq, ndiv_eq]
  exact Nat.add_le_add_right (Nat.div_le_div_right h) 1

theorem norm6 (a b c d e f : ℂ) :
    ‖a + b - c - d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le a b
  have h2 := norm_sub_le (a + b) c
  have h3 := norm_sub_le (a + b - c) d
  have h4 := norm_sub_le (a + b - c - d) e
  have h5 := norm_add_le (a + b - c - d - e) f
  linarith

/-- **The box theorem**: a passing box (kernel-checked flags and final test) has no zero of ζ. -/
theorem boxT_sound {SC TC RS RT : ℕ} {acc : Acc} {s : ℂ}
    (hs1 : |281474976710656 * s.re - SC| ≤ RS) (hs2 : |281474976710656 * s.im - TC| ≤ RT)
    (hσ : 0 < s.re)
    (hI : TInv s (cof SC TC) acc (Fsum (cof SC TC)) (Fsum s) (dsum (cof SC TC)))
    (hW : acc.w.v = true → acc.w.Mem (W 10 (cof SC TC)))
    (hFv : (Fof SC TC acc.F acc.w).v = true) (hdSv : acc.dS.v = true)
    (hSR : SC + RS ≤ 281474976710656) (hRT : RT < TC) (hxN : xNof (RS + RT) ≤ 281474976710656)
    (hfin : boundT SC TC RS RT acc.q acc.w acc.dS * boundT SC TC RS RT acc.q acc.w acc.dS <
      (dist (Fof SC TC acc.F acc.w).a - (Fof SC TC acc.F acc.w).r) *
        (dist (Fof SC TC acc.F acc.w).a - (Fof SC TC acc.F acc.w).r) +
      (dist (Fof SC TC acc.F acc.w).b - (Fof SC TC acc.F acc.w).r) *
        (dist (Fof SC TC acc.F acc.w).b - (Fof SC TC acc.F acc.w).r)) :
    riemannZeta s ≠ 0 := by
  have hS : (0 : ℝ) < 281474976710656 := by norm_num
  obtain ⟨b1, b2⟩ := abs_le.mp hs2
  have hRT' : (RT : ℝ) < TC := by exact_mod_cast hRT
  have hSC : SC ≤ 281474976710656 := by omega
  have hTC0 : 0 < TC := by omega
  have hρ : 281474976710656 * ‖s - cof SC TC‖ ≤ ((RS + RT : ℕ) : ℝ) := srho hs1 hs2
  obtain ⟨hF0v, hwv⟩ := Fof_v hFv
  have hwm := hW hwv
  have hFm : (Fof SC TC acc.F acc.w).Mem (Fval (cof SC TC)) := Fof_mem hFv (hI.1 hF0v) hwm hSC hTC0
  have hlow := center_lower hFm hfin
  have hq := hI.2.2 hF0v
  have hdm := hI.2.1 hdSv
  have hwc := magub_ge hwm
  have hδ := Wdiff hρ hxN
  have him : 0 < s.im := by
    have : (0 : ℝ) < 281474976710656 * s.im := by linarith
    linarith
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at him; simp at him
  have hem := em3_bound s hσ hs1'
  have hxs : up (Nat.mul RS 648120085424804) 281474976710656 ≤ 281474976710656 :=
    le_trans (up_mono _ _ _ (Nat.mul_le_mul_right _ (Nat.le_add_right RS RT))) hxN
  have bL1' := L1_sound hRT (by linarith) hρ hwc hδ
  have bL2' := L2_sound hwc hδ
  have bL3' := L3_sound hρ hwc hδ
  have bE' := E_sound hs1 hs2 hσ hRT hxs hwc
  have bD' := D1_sound hρ hdm
  have hE2 : 281474976710656 * ‖riemannZeta s - Fval s‖ ≤ (bE SC TC RS RT (magub acc.w) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hem hS.le) bE'
  have eq : riemannZeta s - Fval (cof SC TC) =
      (riemannZeta s - Fval s) + (Fsum s - Fsum (cof SC TC) + (s - cof SC TC) * dsum (cof SC TC)) -
        (s - cof SC TC) * dsum (cof SC TC) -
        (10 * W 10 s * (1 - s)⁻¹ - 10 * W 10 (cof SC TC) * (1 - cof SC TC)⁻¹) -
        (W 10 s - W 10 (cof SC TC)) / ((2 : ℕ) : ℂ) +
        (s * W 10 s - cof SC TC * W 10 (cof SC TC)) / ((120 : ℕ) : ℂ) := by
    unfold Fval; ring
  have tri := norm6 (riemannZeta s - Fval s)
    (Fsum s - Fsum (cof SC TC) + (s - cof SC TC) * dsum (cof SC TC))
    ((s - cof SC TC) * dsum (cof SC TC))
    (10 * W 10 s * (1 - s)⁻¹ - 10 * W 10 (cof SC TC) * (1 - cof SC TC)⁻¹)
    ((W 10 s - W 10 (cof SC TC)) / ((2 : ℕ) : ℂ))
    ((s * W 10 s - cof SC TC * W 10 (cof SC TC)) / ((120 : ℕ) : ℂ))
  rw [← eq] at tri
  intro hz
  have hfc : ‖Fval (cof SC TC)‖ = ‖riemannZeta s - Fval (cof SC TC)‖ := by
    rw [hz, zero_sub, norm_neg]
  rw [boundT_eq] at hlow
  simp only [Nat.add_eq] at hlow
  push_cast at hlow
  rw [hfc] at hlow
  linarith [tri, hq, bL1', bL2', bL3', hE2, bD']

theorem boxN_sound {SC TC RS RT : ℕ} (h : boxN SC TC RS RT = true) (s : ℂ)
    (hs1 : |281474976710656 * s.re - SC| ≤ RS) (hs2 : |281474976710656 * s.im - TC| ≤ RT)
    (hσ : 0 < s.re) : riemannZeta s ≠ 0 := by
  rw [boxN_eq] at h
  generalize hacc : accOf (Nat.add RS RT) SC TC (epow 195103586505167 SC TC)
    (epow 309231868366897 SC TC) (epow 453016498919635 SC TC) (epow 547725013886373 SC TC) = acc at h
  rw [boxT_eq] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hok, hFv⟩, hdSv⟩, -⟩, hSR⟩, hTC64⟩, hRT⟩, hxN⟩, hfin⟩ := h
  have hρ : 281474976710656 * ‖s - cof SC TC‖ ≤ ((Nat.add RS RT : ℕ) : ℝ) := srho hs1 hs2
  rw [← hacc] at hok
  have hz := accOf_ok hok
  have hI := accOf_sound hρ (by omega) hTC64 hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hxN
  rw [hacc] at hI
  have hW : acc.w.v = true → acc.w.Mem (W 10 (cof SC TC)) := by
    rw [← hacc, accOf_w]
    exact cmulW_mem' (k := 10) (by norm_num)
      (epow_mem (by norm_num) (logOK_sound (by norm_num) logOK_2) (by omega) hTC64 hz.1)
      (epow_mem (by norm_num) (logOK_sound (by norm_num) logOK_5) (by omega) hTC64 hz.2.2.1)
  exact boxT_sound hs1 hs2 hσ hI hW hFv hdSv hSR hRT hxN hfin

/-- **The quadtree theorem.** -/
theorem qtOK_sound : ∀ (q : QT) (x0 y0 j : ℕ), qtOK q x0 y0 j = true → ∀ s : ℂ,
    (x0 : ℝ) ≤ 281474976710656 * s.re → 281474976710656 * s.re ≤ (x0 : ℝ) + 2 ^ (j + 1) →
    (y0 : ℝ) ≤ 281474976710656 * s.im → 281474976710656 * s.im ≤ (y0 : ℝ) + 2 ^ (j + 1) →
    0 < s.re → riemannZeta s ≠ 0 := by
  intro q
  induction q with
  | leaf =>
    intro x0 y0 j h s h1 h2 h3 h4 hσ
    rw [qtOK_leaf] at h
    have e : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
    apply boxN_sound h s _ _ hσ
    · simp only [Nat.add_eq, npow_eq]
      push_cast
      rw [abs_le]; constructor <;> linarith
    · simp only [Nat.add_eq, npow_eq]
      push_cast
      rw [abs_le]; constructor <;> linarith
  | node a b c d iha ihb ihc ihd =>
    intro x0 y0 j h s h1 h2 h3 h4 hσ
    cases j with
    | zero =>
      rw [qtOK_node0] at h
      exact absurd h (by decide)
    | succ k =>
      rw [qtOK_node] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
      have ex : ((Nat.add x0 (Nat.pow 2 (k + 1)) : ℕ) : ℝ) = (x0 : ℝ) + 2 ^ (k + 1) := by
        simp only [Nat.add_eq, npow_eq]; push_cast; ring
      have ey : ((Nat.add y0 (Nat.pow 2 (k + 1)) : ℕ) : ℝ) = (y0 : ℝ) + 2 ^ (k + 1) := by
        simp only [Nat.add_eq, npow_eq]; push_cast; ring
      have e2 : (2 : ℝ) ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      rcases le_total (281474976710656 * s.re) ((x0 : ℝ) + 2 ^ (k + 1)) with hx | hx <;>
        rcases le_total (281474976710656 * s.im) ((y0 : ℝ) + 2 ^ (k + 1)) with hy | hy
      · exact iha x0 y0 k ha s h1 hx h3 hy hσ
      · exact ihc x0 _ k hc s h1 hx (by rw [ey]; exact hy) (by rw [ey]; linarith) hσ
      · exact ihb _ y0 k hb s (by rw [ex]; exact hx) (by rw [ex]; linarith) h3 hy hσ
      · exact ihd _ _ k hd s (by rw [ex]; exact hx) (by rw [ex]; linarith) (by rw [ey]; exact hy)
          (by rw [ey]; linarith) hσ

/-! ## Strip [0,1] × [6,7]: quadtree from `sim/trees_sound4_unit.json` (106 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q6_0 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q6_0 : qtOK Q6_0 0 1688849860263936 46 = true := by decide +kernel

def Q6_1 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf)

theorem ok_Q6_1 : qtOK Q6_1 (Nat.add 0 (Nat.pow 2 (46 + 1))) 1688849860263936 46 = true := by decide +kernel

def Q6_2 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q6_2 : qtOK Q6_2 0 (Nat.add 1688849860263936 (Nat.pow 2 (46 + 1))) 46 = true := by decide +kernel

def Q6_3 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf)

theorem ok_Q6_3 : qtOK Q6_3 (Nat.add 0 (Nat.pow 2 (46 + 1))) (Nat.add 1688849860263936 (Nat.pow 2 (46 + 1))) 46 = true := by decide +kernel

theorem ok_Q6 : qtOK (QT.node Q6_0 Q6_1 Q6_2 Q6_3) 0 1688849860263936 47 = true := by
  rw [qtOK_node _ _ _ _ _ _ 46]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨ok_Q6_0, ok_Q6_1⟩, ok_Q6_2⟩, ok_Q6_3⟩

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `6 ≤ Im s ≤ 7`. -/
theorem zeta_ne_zero_s6 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 6 ≤ s.im → s.im ≤ 7 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound (QT.node Q6_0 Q6_1 Q6_2 Q6_3) 0 1688849860263936 47 ok_Q6 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [7,8]: quadtree from `sim/trees_sound4_unit.json` (79 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q7_0 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q7_0 : qtOK Q7_0 0 1970324836974592 46 = true := by decide +kernel

def Q7_1 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf)

theorem ok_Q7_1 : qtOK Q7_1 (Nat.add 0 (Nat.pow 2 (46 + 1))) 1970324836974592 46 = true := by decide +kernel

def Q7_2 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q7_2 : qtOK Q7_2 0 (Nat.add 1970324836974592 (Nat.pow 2 (46 + 1))) 46 = true := by decide +kernel

def Q7_3 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf)

theorem ok_Q7_3 : qtOK Q7_3 (Nat.add 0 (Nat.pow 2 (46 + 1))) (Nat.add 1970324836974592 (Nat.pow 2 (46 + 1))) 46 = true := by decide +kernel

theorem ok_Q7 : qtOK (QT.node Q7_0 Q7_1 Q7_2 Q7_3) 0 1970324836974592 47 = true := by
  rw [qtOK_node _ _ _ _ _ _ 46]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨ok_Q7_0, ok_Q7_1⟩, ok_Q7_2⟩, ok_Q7_3⟩

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `7 ≤ Im s ≤ 8`. -/
theorem zeta_ne_zero_s7 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 7 ≤ s.im → s.im ≤ 8 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound (QT.node Q7_0 Q7_1 Q7_2 Q7_3) 0 1970324836974592 47 ok_Q7 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [8,9]: quadtree from `sim/trees_sound4_unit.json` (52 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q8 : QT :=
  (QT.node (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q8 : qtOK Q8 0 2251799813685248 47 = true := by decide +kernel

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `8 ≤ Im s ≤ 9`. -/
theorem zeta_ne_zero_s8 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 8 ≤ s.im → s.im ≤ 9 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound Q8 0 2251799813685248 47 ok_Q8 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [9,10]: quadtree from `sim/trees_sound4_unit.json` (40 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q9 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q9 : qtOK Q9 0 2533274790395904 47 = true := by decide +kernel

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `9 ≤ Im s ≤ 10`. -/
theorem zeta_ne_zero_s9 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 9 ≤ s.im → s.im ≤ 10 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound Q9 0 2533274790395904 47 ok_Q9 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [10,11]: quadtree from `sim/trees_sound4_unit.json` (40 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q10 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q10 : qtOK Q10 0 2814749767106560 47 = true := by decide +kernel

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `10 ≤ Im s ≤ 11`. -/
theorem zeta_ne_zero_s10 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 10 ≤ s.im → s.im ≤ 11 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound Q10 0 2814749767106560 47 ok_Q10 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [11,12]: quadtree from `sim/trees_sound4_unit.json` (40 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q11 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q11 : qtOK Q11 0 3096224743817216 47 = true := by decide +kernel

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `11 ≤ Im s ≤ 12`. -/
theorem zeta_ne_zero_s11 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 11 ≤ s.im → s.im ≤ 12 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound Q11 0 3096224743817216 47 ok_Q11 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [12,13]: quadtree from `sim/trees_sound4_unit.json` (67 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q12 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf))

theorem ok_Q12 : qtOK Q12 0 3377699720527872 47 = true := by decide +kernel

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `12 ≤ Im s ≤ 13`. -/
theorem zeta_ne_zero_s12 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 12 ≤ s.im → s.im ≤ 13 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound Q12 0 3377699720527872 47 ok_Q12 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-! ## Strip [0,1] × [13,14]: quadtree from `sim/trees_sound4_unit.json` (214 leaves, all re-checked against `sim/zbox_sound4.py`), chunks of ≤ 72 leaves -/

def Q13_0 : QT :=
  (QT.node (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf))

theorem ok_Q13_0 : qtOK Q13_0 0 3659174697238528 46 = true := by decide +kernel

def Q13_1 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q13_1 : qtOK Q13_1 (Nat.add 0 (Nat.pow 2 (46 + 1))) 3659174697238528 46 = true := by decide +kernel

def Q13_2_0 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q13_2_0 : qtOK Q13_2_0 0 (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) 45 = true := by decide +kernel

def Q13_2_1 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf))

theorem ok_Q13_2_1 : qtOK Q13_2_1 (Nat.add 0 (Nat.pow 2 (45 + 1))) (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) 45 = true := by decide +kernel

def Q13_2_2 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)))

theorem ok_Q13_2_2 : qtOK Q13_2_2 0 (Nat.add (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) (Nat.pow 2 (45 + 1))) 45 = true := by decide +kernel

def Q13_2_3 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)))

theorem ok_Q13_2_3 : qtOK Q13_2_3 (Nat.add 0 (Nat.pow 2 (45 + 1))) (Nat.add (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) (Nat.pow 2 (45 + 1))) 45 = true := by decide +kernel

theorem ok_Q13_2 : qtOK (QT.node Q13_2_0 Q13_2_1 Q13_2_2 Q13_2_3) 0 (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) 46 = true := by
  rw [qtOK_node _ _ _ _ _ _ 45]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨ok_Q13_2_0, ok_Q13_2_1⟩, ok_Q13_2_2⟩, ok_Q13_2_3⟩

def Q13_3 : QT :=
  (QT.node (QT.node QT.leaf QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf QT.leaf QT.leaf)) (QT.node QT.leaf QT.leaf (QT.node QT.leaf QT.leaf QT.leaf QT.leaf) QT.leaf))

theorem ok_Q13_3 : qtOK Q13_3 (Nat.add 0 (Nat.pow 2 (46 + 1))) (Nat.add 3659174697238528 (Nat.pow 2 (46 + 1))) 46 = true := by decide +kernel

theorem ok_Q13 : qtOK (QT.node Q13_0 Q13_1 (QT.node Q13_2_0 Q13_2_1 Q13_2_2 Q13_2_3) Q13_3) 0 3659174697238528 47 = true := by
  rw [qtOK_node _ _ _ _ _ _ 46]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨ok_Q13_0, ok_Q13_1⟩, ok_Q13_2⟩, ok_Q13_3⟩

/-- **Strip region theorem**: no zero of ζ in `0 < Re s < 1`, `13 ≤ Im s ≤ 14`. -/
theorem zeta_ne_zero_s13 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 13 ≤ s.im → s.im ≤ 14 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  exact qtOK_sound (QT.node Q13_0 Q13_1 (QT.node Q13_2_0 Q13_2_1 Q13_2_2 Q13_2_3) Q13_3) 0 3659174697238528 47 ok_Q13 s (by norm_num <;> linarith) (by norm_num <;> linarith)
    (by norm_num <;> linarith) (by norm_num <;> linarith) h0

/-- **Region `6 ≤ Im s ≤ 14`** from the eight unit strips. -/
theorem zeta_ne_zero_6_14 : ∀ s : ℂ, 0 < s.re → s.re < 1 → 6 ≤ s.im → s.im ≤ 14 → riemannZeta s ≠ 0 := by
  intro s h0 h1 h2 h3
  rcases le_total s.im 7 with g6 | g6
  · exact zeta_ne_zero_s6 s h0 h1 h2 g6
  rcases le_total s.im 8 with g7 | g7
  · exact zeta_ne_zero_s7 s h0 h1 g6 g7
  rcases le_total s.im 9 with g8 | g8
  · exact zeta_ne_zero_s8 s h0 h1 g7 g8
  rcases le_total s.im 10 with g9 | g9
  · exact zeta_ne_zero_s9 s h0 h1 g8 g9
  rcases le_total s.im 11 with g10 | g10
  · exact zeta_ne_zero_s10 s h0 h1 g9 g10
  rcases le_total s.im 12 with g11 | g11
  · exact zeta_ne_zero_s11 s h0 h1 g10 g11
  rcases le_total s.im 13 with g12 | g12
  · exact zeta_ne_zero_s12 s h0 h1 g11 g12
  exact zeta_ne_zero_s13 s h0 h1 g12 h3

end ZFrame


/-- `ζ(s) ≠ 0` for `0 < Re s < 1`, `2 ≤ Im s ≤ 14` (port of the certificate of
`TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen`). -/
theorem ZFrame.zeta_ne_zero_two_to_fourteen (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 2 ≤ s.im) (hb : s.im ≤ 14) : riemannZeta s ≠ 0 := by
  rcases le_total s.im 6 with h6 | h6
  · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_six s h0 h1 (abs_le.2 ⟨by linarith, h6⟩)
  · exact ZFrame.zeta_ne_zero_6_14 s h0 h1 h6 hb

/-- Zero-free rectangle `0 < Re s < 1`, `|Im s| ≤ 14`. -/
theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 14) : riemannZeta s ≠ 0 := by
  rcases le_total |s.im| 6 with h6 | h6
  · exact zeta_ne_zero_of_mem_strip_of_abs_im_le_six s h0 h1 h6
  rcases le_total 0 s.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at h6 him
    exact ZFrame.zeta_ne_zero_two_to_fourteen s h0 h1 (by linarith) him
  · rw [abs_of_nonpos hneg] at h6 him
    intro hz
    have hc : riemannZeta ((starRingEnd ℂ) s) = 0 := by
      rw [riemannZeta_conj, hz, map_zero]
    refine ZFrame.zeta_ne_zero_two_to_fourteen ((starRingEnd ℂ) s) ?_ ?_ ?_ ?_ hc
    · simpa using h0
    · simpa using h1
    · simp; linarith
    · simp; linarith

#print axioms solution
