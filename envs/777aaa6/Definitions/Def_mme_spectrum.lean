-- Prove2me | Definitions.Def_mme_spectrum
-- name    : mme_spectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:32:56.121468+00:00
-- url     : https://prove2.me/theorems/b0bb4750-93c6-4757-8f23-293d97e99519
-- statement:
--   **Asymptotic spectrum points, rank facts, and the deep spectrum leaves.**
--
--   The abstract backbone for Strassen's $\tau$-theorem on top of `MME.StrassenPreorder`, adapted from Wigderson–Zuiddam / the Prism `AsymptoticSpectra` development. Built directly over `Def_mme_strassen_preorder` — no quotient or tensor machinery.
--
--   **Rank facts (sorry-free).**
--   - `rank_one`, `rank_monotone`, `rank_submultiplicative`, `pow_ne_zero`, `rank_pow_ge_one` — the basic algebraic properties of `StrassenPreorder.rank`.
--
--   **The asymptotic spectrum.** `AsymptoticSpectrumPoint P` is a *monotone ring homomorphism* $\varphi : R \to \mathbb{R}$ with $\varphi(\mathbb{N}) = \mathbb{N}$ (preserves natural numbers) and respecting $P$'s order. The file installs the standard `FunLike` / `RingHomClass` instances, the topology of pointwise convergence, and proves `continuous_eval` (every evaluation $\varphi \mapsto \varphi(a)$ is continuous) and compactness of the spectrum.
--
--   **Three deep `sorry` leaves** (the analytic core, proved elsewhere or downstream):
--   - `tends_to_asymptoticRank` — Fekete convergence: $\mathrm{rank}_P(a^{n})^{1/n}$ converges to $\mathrm{asymptoticRank}_P(a)$.
--   - `AsymptoticSpectrumPoint.nonempty` — every Strassen preorder has at least one spectrum point (existence via Zorn / total extension; proved in `Def_mme_duality`).
--   - `asymptoticRank_eq_sup_spectrum` — **Strassen duality**: $\mathrm{asymptoticRank}_P(a) = \sup_{\varphi} \varphi(a)$ over the spectrum (proved in `Def_mme_duality`).
--
--   These three are the "engine" of the asymptotic-spectrum theory; everything else in MME builds on them.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_mme_strassen_preorder

/-! # Asymptotic spectrum and duality for abstract Strassen preorders (MME)

The abstract backbone for Strassen's `τ` theorem, adapted from
Wigderson–Zuiddam / the Prism `AsymptoticSpectra` development to the lightweight
`MME.StrassenPreorder` structure of `Def_mme_strassen_preorder`.

This file:

* proves the elementary `rank` facts (`rank_one`, `rank_monotone`,
  `rank_submultiplicative`, `pow_ne_zero`, `rank_pow_ge_one`) — all sorry-free;
* defines `AsymptoticSpectrumPoint P` (a monotone semiring hom `R →+* ℝ`),
  installs its `FunLike`/`RingHomClass`/topology instances, and proves
  `continuous_eval` and compactness — all sorry-free;
* isolates the two genuinely deep facts as named `sorry` leaves:
  - `AsymptoticSpectrumPoint.nonempty`     (existence of a spectrum point — needs the
    Zorn/total-extension argument),
  - `asymptoticRank_eq_sup_spectrum`        (Strassen **duality** — `AR a = ⨆_φ φ a`),
  - `tends_to_asymptoticRank`               (Fekete convergence of normalized rank).

Everything downstream (the MM evaluation, Jensen averaging, and the final
sum-inequality assembly) is then built sorry-free on top of these three. -/

universe u

open Filter Topology BigOperators
open scoped Classical

namespace MME

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R] (P : StrassenPreorder R)

/-! ## Elementary rank facts (sorry-free) -/

/-- The defining set `{n | a ≤ n}` of `rank a` is nonempty (upper Archimedean). -/
theorem rank_set_nonempty (a : R) : {n : ℕ | P.le a (n : R)}.Nonempty :=
  P.upper_archimedean a

/-- `a ≤ rank a` for the canonical witness `sInf`. -/
theorem le_rank (a : R) : P.le a ((rank P a : ℕ) : R) :=
  Nat.sInf_mem (rank_set_nonempty P a)

theorem rank_le_of_le {a : R} {n : ℕ} (h : P.le a (n : R)) : rank P a ≤ n :=
  Nat.sInf_le h

theorem rank_monotone {a b : R} (h : P.le a b) : rank P a ≤ rank P b := by
  apply rank_le_of_le
  exact P.le_trans _ _ _ h (le_rank P b)

theorem rank_submultiplicative (a b : R) : rank P (a * b) ≤ rank P a * rank P b := by
  apply rank_le_of_le
  rw [Nat.cast_mul]
  apply P.le_trans (a * b) ((rank P a : R) * b) ((rank P a : R) * (rank P b : R))
  · exact P.mul_right a (rank P a : R) (le_rank P a) b
  · rw [mul_comm (rank P a : R), mul_comm (rank P a : R)]
    exact P.mul_right b (rank P b : R) (le_rank P b) (rank P a : R)

theorem rank_subadditive (a b : R) : rank P (a + b) ≤ rank P a + rank P b := by
  apply rank_le_of_le
  rw [Nat.cast_add]
  apply P.le_trans (a + b) ((rank P a : R) + b) ((rank P a : R) + (rank P b : R))
  · exact P.add_right a (rank P a : R) (le_rank P a) b
  · rw [add_comm (rank P a : R), add_comm (rank P a : R)]
    exact P.add_right b (rank P b : R) (le_rank P b) (rank P a : R)

theorem not_le_one_zero : ¬ P.le (1 : R) (0 : R) := by
  rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding]
  exact Nat.not_succ_le_zero 0

theorem rank_one : rank P (1 : R) = 1 := by
  apply le_antisymm
  · apply rank_le_of_le
    rw [Nat.cast_one]; exact P.le_refl _
  · rcases Nat.eq_zero_or_pos (rank P (1 : R)) with h | h
    · exfalso
      have hspec := le_rank P (1 : R)
      rw [h, Nat.cast_zero] at hspec
      exact not_le_one_zero P hspec
    · exact h

theorem one_le_rank_of_ne_zero {a : R} (ha : a ≠ 0) : 1 ≤ rank P a := by
  rcases P.lower_archimedean a with h | h
  · exact absurd h ha
  · have := rank_monotone P h
    rwa [rank_one] at this

theorem toNoZeroDivisors (P : StrassenPreorder R) : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_cases ha : a = 0; · left; exact ha
    by_cases hb : b = 0; · right; exact hb
    exfalso
    have h1 : P.le (1 : R) (a * b) := by
      apply P.le_trans (1 : R) a (a * b)
      · rcases P.lower_archimedean a with h | h; · exact absurd h ha
        · exact h
      · rw [mul_comm]
        rcases P.lower_archimedean b with h | h; · exact absurd h hb
        · simpa [mul_comm] using P.mul_right 1 b h a
    rw [h] at h1
    exact not_le_one_zero P h1

theorem pow_ne_zero (P : StrassenPreorder R) (n : ℕ) {a : R} (ha : a ≠ 0) : a ^ n ≠ 0 :=
  letI := P.toNoZeroDivisors
  _root_.pow_ne_zero n ha

theorem one_le_pow_of_ne_zero {a : R} (ha : a ≠ 0) (n : ℕ) : P.le 1 (a ^ n) := by
  rcases P.lower_archimedean a with h | h
  · exact absurd h ha
  · induction n with
    | zero => simpa using P.le_refl (1 : R)
    | succ n ih =>
      rw [pow_succ, mul_comm]
      have h_mul := P.mul_right 1 a h (a ^ n)
      rw [one_mul] at h_mul
      exact P.le_trans 1 (a ^ n) (a * a ^ n) ih h_mul

theorem rank_pow_ge_one {a : R} (ha : a ≠ 0) (n : ℕ) : 1 ≤ (rank P (a ^ n) : ℝ) := by
  have h := rank_monotone P (one_le_pow_of_ne_zero P ha n)
  rw [rank_one] at h
  exact_mod_cast h

/-! ## The convergence of normalized rank (Fekete) — deep leaf -/

/-- **Fekete convergence of asymptotic rank** (deep leaf).

The normalized rank `rank(aⁿ)^(1/n)` converges to `asymptoticRank a`. By Fekete's
lemma applied to the submultiplicative sequence `n ↦ rank(aⁿ)` (bounded below by `1`
for `a ≠ 0`). The MME `asymptoticRank` is the `⨅` over `n+1`; this lemma is the
statement that that infimum is the limit of the `n`-th roots.

Self-contained via Mathlib's `Subadditive.tendsto_lim` applied to `v = log (rank (aⁿ))`,
then the algebra identifying `asymptoticRank = ⨅ₙ rank(aⁿ⁺¹)^(1/(n+1))` with the
Fekete infimum `sInf (rank(aⁿ)^(1/n) '' Ici 1)`. -/
theorem tends_to_asymptoticRank {a : R} (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => (rank P (a ^ n) : ℝ) ^ (1 / (n : ℝ))) atTop
      (nhds (asymptoticRank P a)) := by
  -- The base sequence `u n = rank (aⁿ)`: submultiplicative and `≥ 1` (for `a ≠ 0`).
  set u : ℕ → ℝ := fun n => (rank P (a ^ n) : ℝ) with hu
  have hu1 : ∀ n, 1 ≤ u n := fun n => rank_pow_ge_one P ha n
  have hupos : ∀ n, 0 < u n := fun n => lt_of_lt_of_le one_pos (hu1 n)
  -- `v = log u` is subadditive (from submultiplicativity of rank under `a^(m+n)=aᵐaⁿ`).
  set v : ℕ → ℝ := fun n => Real.log (u n) with hv
  have hvsub : Subadditive v := by
    intro m n
    simp only [hv]
    rw [← Real.log_mul (hupos m).ne' (hupos n).ne']
    refine Real.log_le_log (hupos (m + n)) ?_
    have hmn : rank P (a ^ (m + n)) ≤ rank P (a ^ m) * rank P (a ^ n) := by
      rw [pow_add]; exact rank_submultiplicative P _ _
    simp only [hu]
    exact_mod_cast hmn
  have hvbdd : BddBelow (Set.range fun n => v n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (Real.log_nonneg (hu1 n)) (Nat.cast_nonneg n)
  -- Fekete (Mathlib): `v n / n → Subadditive.lim`; exponentiate to `u n ^ (1/n)`.
  have hvlim : Tendsto (fun n => v n / n) atTop (nhds hvsub.lim) := hvsub.tendsto_lim hvbdd
  have hexp : Tendsto (fun n => Real.exp (v n / n)) atTop (nhds (Real.exp hvsub.lim)) :=
    (Real.continuous_exp.tendsto _).comp hvlim
  have heq : ∀ n : ℕ, n ≠ 0 → Real.exp (v n / n) = u n ^ (1 / (n : ℝ)) := by
    intro n _
    simp only [hv]
    rw [div_eq_mul_one_div, Real.exp_mul, Real.exp_log (hupos n)]
  have hg : Tendsto (fun n : ℕ => u n ^ (1 / (n : ℝ))) atTop (nhds (Real.exp hvsub.lim)) :=
    hexp.congr' (eventually_atTop.2 ⟨1, fun n hn => heq n (Nat.one_le_iff_ne_zero.mp hn)⟩)
  -- Identify the Fekete limit with `asymptoticRank` (both are `sInf (u ·^(1/·) '' Ici 1)`).
  have hlim : asymptoticRank P a = Real.exp hvsub.lim := by
    have hsets : (fun n : ℕ => u n ^ (1 / (n : ℝ))) '' Set.Ici 1
        = Real.exp '' ((fun n : ℕ => v n / n) '' Set.Ici 1) := by
      rw [Set.image_image]
      exact Set.image_congr (fun n hn => (heq n (Nat.one_le_iff_ne_zero.mp hn)).symm)
    have hcomm : sInf ((fun n : ℕ => u n ^ (1 / (n : ℝ))) '' Set.Ici 1) = Real.exp hvsub.lim := by
      rw [hsets, Subadditive.lim]
      exact (Monotone.map_csInf_of_continuousAt Real.continuous_exp.continuousAt Real.exp_monotone
        (Set.Nonempty.image _ ⟨1, Set.mem_Ici.mpr le_rfl⟩)
        (hvbdd.mono (Set.image_subset_range _ _))).symm
    rw [← hcomm, asymptoticRank, iInf]
    congr 1
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n + 1, Set.mem_Ici.mpr (Nat.le_add_left 1 n), ?_⟩
      simp only [hu, Nat.cast_add, Nat.cast_one]
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Set.mem_Ici.mp hm)
      refine ⟨n, ?_⟩
      simp only [hu, Nat.cast_add, Nat.cast_one, add_comm n 1]
      rw [add_comm (n : ℝ) 1]
  rw [hlim]; exact hg

end StrassenPreorder

/-! ## Asymptotic spectrum points -/

/-- A point in the asymptotic spectrum: a semiring homomorphism `R →+* ℝ` that is
monotone for the preorder `P`. -/
structure AsymptoticSpectrumPoint (R : Type u) [CommSemiring R] (P : StrassenPreorder R)
    extends R →+* ℝ where
  monotone' : ∀ {a b : R}, P.le a b → toRingHom a ≤ toRingHom b

namespace AsymptoticSpectrumPoint

variable {R : Type u} [CommSemiring R] {P : StrassenPreorder R}

instance instFunLike : FunLike (AsymptoticSpectrumPoint R P) R ℝ where
  coe f := f.toRingHom.toFun
  coe_injective' f g h := by
    obtain ⟨f_hom, f_mono⟩ := f
    obtain ⟨g_hom, g_mono⟩ := g
    congr
    exact DFunLike.coe_injective h

instance instRingHomClass : RingHomClass (AsymptoticSpectrumPoint R P) R ℝ where
  map_add f := f.toRingHom.map_add'
  map_mul f := f.toRingHom.map_mul'
  map_zero f := f.toRingHom.map_zero'
  map_one f := f.toRingHom.map_one'

@[ext]
theorem ext (φ ψ : AsymptoticSpectrumPoint R P) (h : ∀ a, φ a = ψ a) : φ = ψ :=
  DFunLike.ext φ ψ h

/-- `0 ≤ φ a` for any spectrum point (every element is `≥ 0`). -/
theorem nonneg (φ : AsymptoticSpectrumPoint R P) (a : R) : 0 ≤ φ a := by
  have := φ.monotone' (P.zero_le a)
  rwa [map_zero] at this

/-- The topology on the asymptotic spectrum is the topology of pointwise convergence. -/
instance instTopologicalSpace : TopologicalSpace (AsymptoticSpectrumPoint R P) :=
  TopologicalSpace.induced (fun f => (f : R → ℝ)) Pi.topologicalSpace

theorem continuous_eval (a : R) :
    Continuous (fun (φ : AsymptoticSpectrumPoint R P) => φ a) :=
  continuous_pi_iff.mp continuous_induced_dom a

/-! ### Compactness via the bounding box -/

/-- The product of intervals `[0, rank a]` that contains the spectrum. -/
def SpectrumBox (P : StrassenPreorder R) : Type u :=
  ∀ a : R, ↥(Set.Icc (0 : ℝ) (StrassenPreorder.rank P a : ℝ))

instance : TopologicalSpace (SpectrumBox P) := Pi.topologicalSpace
instance : CompactSpace (SpectrumBox P) := Pi.compactSpace
instance : T2Space (SpectrumBox P) := Pi.t2Space

/-- The natural map from spectrum points to the box. -/
def toBox (φ : AsymptoticSpectrumPoint R P) : SpectrumBox P :=
  fun a => ⟨φ a, by
    refine ⟨nonneg φ a, ?_⟩
    have := φ.monotone' (StrassenPreorder.le_rank P a)
    rwa [map_natCast] at this⟩

theorem continuous_toBox : Continuous (toBox (P := P)) := by
  apply continuous_pi
  intro a
  exact Continuous.subtype_mk (continuous_eval a) _

theorem embedding_toBox : IsEmbedding (toBox (P := P)) := by
  let coeBox : SpectrumBox P → (R → ℝ) := fun f a => (f a : ℝ)
  -- `coeBox` is inducing (it embeds the product of subtype-coercions).
  have h_box_ind : IsInducing (coeBox) := by
    rw [isInducing_iff]
    show (Pi.topologicalSpace : TopologicalSpace (SpectrumBox P)) = _
    simp only [Pi.topologicalSpace, induced_iInf, induced_compose]
    congr; funext a
    have : IsEmbedding (Subtype.val :
        Set.Icc (0:ℝ) (StrassenPreorder.rank P a : ℝ) → ℝ) := IsEmbedding.subtypeVal
    rw [this.eq_induced]
    simp only [induced_compose]; rfl
  -- The coercion `φ ↦ (φ : R → ℝ)` is inducing (the spectrum's defining topology).
  have h_coe_ind : IsInducing (fun φ : AsymptoticSpectrumPoint R P => (φ : R → ℝ)) := by
    rw [isInducing_iff]; rfl
  -- `coeBox ∘ toBox = coercion`, so `toBox` is inducing.
  have h_comp : coeBox ∘ (toBox (P := P)) =
      (fun φ : AsymptoticSpectrumPoint R P => (φ : R → ℝ)) := by
    funext φ; funext a; rfl
  have h_toBox_ind : IsInducing (toBox (P := P)) := by
    have hiff := h_box_ind.of_comp_iff (f := toBox (P := P))
    rw [h_comp] at hiff
    exact hiff.mp h_coe_ind
  refine ⟨h_toBox_ind, ?_⟩
  intro φ ψ h
  ext a
  have := congr_fun h a
  rw [Subtype.ext_iff] at this
  exact this

theorem isClosed_range_toBox : IsClosed (Set.range (toBox (P := P))) := by
  let f_val (a : R) : SpectrumBox P → ℝ := fun f => (f a : ℝ)
  have h_val (a : R) : Continuous (f_val a) := (continuous_apply a).subtype_val
  let S_add := {f : SpectrumBox P | ∀ a b, f_val (a + b) f = f_val a f + f_val b f}
  let S_mul := {f : SpectrumBox P | ∀ a b, f_val (a * b) f = f_val a f * f_val b f}
  let S_zero := {f : SpectrumBox P | f_val 0 f = 0}
  let S_one := {f : SpectrumBox P | f_val 1 f = 1}
  let S_mono := {f : SpectrumBox P | ∀ a b, P.le a b → f_val a f ≤ f_val b f}
  have h_cl : IsClosed (S_add ∩ S_mul ∩ S_zero ∩ S_one ∩ S_mono) := by
    repeat' apply IsClosed.inter
    · simp only [S_add, Set.setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (h_val _) ((h_val _).add (h_val _))
    · simp only [S_mul, Set.setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (h_val _) ((h_val _).mul (h_val _))
    · exact isClosed_eq (h_val 0) continuous_const
    · exact isClosed_eq (h_val 1) continuous_const
    · simp only [S_mono, Set.setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_le (h_val _) (h_val _)
  have h_eq : Set.range (toBox (P := P)) =
      S_add ∩ S_mul ∩ S_zero ∩ S_one ∩ S_mono := by
    ext f
    constructor
    · rintro ⟨φ, rfl⟩
      simp only [Set.mem_inter_iff, S_add, S_mul, S_zero, S_one, S_mono, Set.mem_setOf_eq]
      exact ⟨⟨⟨⟨fun a b => map_add φ a b, fun a b => map_mul φ a b⟩, map_zero φ⟩,
        map_one φ⟩, fun a b hab => φ.monotone' hab⟩
    · intro h
      rcases h with ⟨⟨⟨⟨h_add, h_mul⟩, h_zero⟩, h_one⟩, h_mono⟩
      let φ_hom : R →+* ℝ :=
        { toFun := fun a => f_val a f, map_add' := h_add, map_mul' := h_mul,
          map_zero' := h_zero, map_one' := h_one }
      let φ : AsymptoticSpectrumPoint R P :=
        { toRingHom := φ_hom, monotone' := fun {a b} hab => h_mono a b hab }
      exact ⟨φ, funext fun a => Subtype.ext rfl⟩
  rw [h_eq]; exact h_cl

instance instCompactSpace : CompactSpace (AsymptoticSpectrumPoint R P) :=
  ⟨by
    rw [embedding_toBox.isCompact_iff, Set.image_univ]
    exact IsClosed.isCompact isClosed_range_toBox⟩

instance instT2Space : T2Space (AsymptoticSpectrumPoint R P) :=
  T2Space.of_injective_continuous embedding_toBox.injective continuous_toBox

-- `nonempty` (existence of spectrum points) is proved in `Def_mme_duality.lean` as
-- `mme_spectrum_nonempty` (Zorn `total_extension` + `rho_toRingHom`), where it provides
-- the `Nonempty (AsymptoticSpectrumPoint R P)` instance.

end AsymptoticSpectrumPoint

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R] (P : StrassenPreorder R)

-- **Strassen duality** (`asymptoticRank P a = ⨆ φ, φ a`) is proved in
-- `Def_mme_duality.lean` as `mme_strassen_duality`, and `eval_le_asymptoticRank`
-- (`φ a ≤ asymptoticRank P a`) lives there too. Only the sorry-free bound below stays here.

/-- The spectrum-point evaluations are bounded above (by `rank a`), so the `⨆` is
genuine. Sorry-free. -/
theorem spectrum_eval_bddAbove (a : R) :
    BddAbove (Set.range (fun φ : AsymptoticSpectrumPoint R P => φ a)) := by
  refine ⟨(rank P a : ℝ), ?_⟩
  rintro _ ⟨φ, rfl⟩
  have := φ.monotone' (le_rank P a)
  rwa [map_natCast] at this

end StrassenPreorder

end MME


