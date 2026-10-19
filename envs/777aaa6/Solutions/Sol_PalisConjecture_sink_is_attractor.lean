-- Prove2me | solution 1 for PalisConjecture.sink_is_attractor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:38:08.867066+00:00
-- url     : https://prove2.me/submissions/a82c8a3c-bd02-4de8-9542-876c1d9d9d74

import Mathlib
import Definitions.Def_palis_lebesgue_null
import Definitions.Def_palis_attractor
import Definitions.Def_palis_vector_field
import Definitions.Def_palis_cr_topology

open scoped Manifold ContDiff
open Set Filter Topology

namespace PalisSink

lemma hasFDeriv_chart (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M) (p : M) (hp : f p = p)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (hpe : p ∈ e.source) :
    HasFDerivAt (e ∘ f ∘ e.symm) (fderiv ℝ (e ∘ f ∘ e.symm) (e p)) (e p) := by
  haveI : IsManifold (𝓡 n) (r : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hmax : e ∈ IsManifold.maximalAtlas (𝓡 n) (r : WithTop ℕ∞) M :=
    IsManifold.subset_maximalAtlas he
  have hc : ContMDiffWithinAt (𝓡 n) (𝓡 n) (r : WithTop ℕ∞) f Set.univ p :=
    f.contMDiff.contMDiffAt.contMDiffWithinAt
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas hmax hmax hpe (by rw [hp]; exact hpe)] at hc
  obtain ⟨_, hd⟩ := hc
  simp only [Set.preimage_univ, Set.univ_inter, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Set.range_id, Function.id_comp, Function.comp_id,
    contDiffWithinAt_univ, id_eq] at hd
  have hne : (r : WithTop ℕ∞) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : WithTop ℕ∞ => ENat.toNat (WithTop.untopD 0 x)) h
    change r = 0 at h2
    omega
  exact (hd.differentiableAt hne).hasFDerivAt


lemma omega_sub {M : Type*} [TopologicalSpace M] [T2Space M] (T : M → M) (q p : M)
    (h : Tendsto (fun k => T^[k] q) atTop (𝓝 p)) : PalisConjecture.omegaLimitMap T q ⊆ {p} := by
  intro y hy
  by_contra hyp
  rw [Set.mem_singleton_iff] at hyp
  obtain ⟨Uy, Vp, hUy, hVp, hyU, hpV, hdisj⟩ := t2_separation hyp
  have hu : {k : ℕ | T^[k] q ∈ Vp} ∈ (atTop : Filter ℕ) := h (hVp.mem_nhds hpV)
  unfold PalisConjecture.omegaLimitMap at hy
  rw [omegaLimit_def] at hy
  have := Set.mem_iInter₂.1 hy _ hu
  have hsub : Set.image2 (fun (k : ℕ) (x : M) => T^[k] x) {k : ℕ | T^[k] q ∈ Vp} {q} ⊆ Vp := by
    rintro _ ⟨k, hk, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx; subst hx; exact hk
  have hy' := closure_mono hsub this
  rw [mem_closure_iff] at hy'
  obtain ⟨z, hz1, hz2⟩ := hy' Uy hUy hyU
  exact Set.disjoint_left.1 hdisj hz1 hz2

lemma contract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → E) (x0 : E)
    (hg : g x0 = x0) (A : E →L[ℝ] E) (hA : HasFDerivAt g A x0) (N : ℕ) (hN : ‖A ^ N‖ < 1)
    (V : Set E) (hV : V ∈ 𝓝 x0) :
    ∃ U ∈ 𝓝 x0, ∀ x ∈ U, (∀ k, g^[k] x ∈ V) ∧ Tendsto (fun k => g^[k] x) atTop (𝓝 x0) := by
  have hfix : ∀ j, g^[j] x0 = x0 := fun j => Function.iterate_fixed hg j
  have hcont : ∀ j, ContinuousAt (g^[j]) x0 := fun j => (hA.iterate hg j).continuousAt
  -- uniform continuity of the finitely many iterates
  have hunif : ∀ S ∈ 𝓝 x0, ∀ᶠ y in 𝓝 x0, ∀ j : Fin (N + 1), g^[(j : ℕ)] y ∈ S := by
    intro S hS
    rw [Filter.eventually_all]
    intro j
    have := (hcont j).preimage_mem_nhds (by rw [hfix]; exact hS)
    exact this
  by_cases hN0 : N = 0
  · subst hN0
    -- then the space is trivial
    have hsub : Subsingleton E := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      simp at hN
    refine ⟨Set.univ, Filter.univ_mem, fun x _ => ⟨fun k => ?_, ?_⟩⟩
    · rw [Subsingleton.elim (g^[k] x) x0]; exact mem_of_mem_nhds hV
    · have : (fun k => g^[k] x) = fun _ => x0 := funext (fun k => Subsingleton.elim _ _)
      rw [this]; exact tendsto_const_nhds
  set B := A ^ N
  set θ := (‖B‖ + 1) / 2 with hθ
  have hθ1 : θ < 1 := by linarith
  have hθ0 : 0 ≤ θ := by positivity
  have hBθ : ‖B‖ < θ := by linarith
  have hh := hA.iterate hg N
  -- contraction estimate near x0
  have hloc : ∀ᶠ x in 𝓝 x0, ‖g^[N] x - x0‖ ≤ θ * ‖x - x0‖ := by
    have := hh.isLittleO.def (show 0 < θ - ‖B‖ by linarith)
    filter_upwards [this] with x hx
    rw [hfix N] at hx
    have h2 : ‖B (x - x0)‖ ≤ ‖B‖ * ‖x - x0‖ := B.le_opNorm _
    calc ‖g^[N] x - x0‖ = ‖(g^[N] x - x0 - B (x - x0)) + B (x - x0)‖ := by congr 1; abel
      _ ≤ ‖g^[N] x - x0 - B (x - x0)‖ + ‖B (x - x0)‖ := norm_add_le _ _
      _ ≤ (θ - ‖B‖) * ‖x - x0‖ + ‖B‖ * ‖x - x0‖ := add_le_add hx h2
      _ = θ * ‖x - x0‖ := by ring
  obtain ⟨δ1, hδ1, hball1⟩ := Metric.eventually_nhds_iff.1 hloc
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨δ2, hδ2, hball2⟩ := Metric.eventually_nhds_iff.1 (hunif _ (Metric.ball_mem_nhds x0 hρ))
  set δ := min δ1 δ2
  have hδ : 0 < δ := lt_min hδ1 hδ2
  refine ⟨Metric.ball x0 δ, Metric.ball_mem_nhds x0 hδ, fun x hx => ?_⟩
  -- iterates by multiples of N
  have hmul : ∀ m, ‖g^[N * m] x - x0‖ ≤ θ ^ m * ‖x - x0‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hin : dist (g^[N * m] x) x0 < δ1 := by
        rw [dist_eq_norm]
        calc ‖g^[N * m] x - x0‖ ≤ θ ^ m * ‖x - x0‖ := ih
          _ ≤ 1 * ‖x - x0‖ := by gcongr; exact pow_le_one₀ hθ0 hθ1.le
          _ < δ1 := by rw [one_mul, ← dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_left _ _)
      have := hball1 hin
      rw [show N * (m + 1) = N + N * m by ring, Function.iterate_add_apply]
      calc ‖g^[N] (g^[N * m] x) - x0‖ ≤ θ * ‖g^[N * m] x - x0‖ := this
        _ ≤ θ * (θ ^ m * ‖x - x0‖) := by gcongr
        _ = θ ^ (m + 1) * ‖x - x0‖ := by ring
  have hdecomp : ∀ k, g^[k] x = g^[k % N] (g^[N * (k / N)] x) := by
    intro k
    rw [← Function.iterate_add_apply]
    congr 1
    exact (Nat.mod_add_div k N).symm
  have hsmall : ∀ m, dist (g^[N * m] x) x0 < δ := by
    intro m
    rw [dist_eq_norm]
    calc ‖g^[N * m] x - x0‖ ≤ θ ^ m * ‖x - x0‖ := hmul m
      _ ≤ 1 * ‖x - x0‖ := by gcongr; exact pow_le_one₀ hθ0 hθ1.le
      _ < δ := by rw [one_mul, ← dist_eq_norm]; exact hx
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  refine ⟨fun k => ?_, ?_⟩
  · rw [hdecomp k]
    have := hball2 (lt_of_lt_of_le (hsmall (k / N)) (min_le_right _ _)) ⟨k % N, by
      have := Nat.mod_lt k hNpos; omega⟩
    exact hρV this
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ3, hδ3, hball3⟩ := Metric.eventually_nhds_iff.1 (hunif _ (Metric.ball_mem_nhds x0 hε))
    have hpow : Tendsto (fun m : ℕ => θ ^ m * ‖x - x0‖) atTop (𝓝 (0 * ‖x - x0‖)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const _
    rw [zero_mul] at hpow
    obtain ⟨m0, hm0⟩ := (Metric.tendsto_atTop.1 hpow) δ3 hδ3
    refine ⟨N * m0, fun k hk => ?_⟩
    rw [hdecomp k]
    have hkm : m0 ≤ k / N := by
      rw [Nat.le_div_iff_mul_le hNpos]; linarith [mul_comm N m0]
    have h1 : dist (g^[N * (k / N)] x) x0 < δ3 := by
      rw [dist_eq_norm]
      have := hm0 (k / N) hkm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
      exact lt_of_le_of_lt (hmul _) this
    exact hball3 h1 ⟨k % N, by have := Nat.mod_lt k hNpos; omega⟩

end PalisSink

open scoped Manifold ContDiff
open Set Filter Topology

namespace PalisSink

theorem sink (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M) (p : M) (hp : f p = p)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (hpe : p ∈ e.source)
    (hsink : ∃ N : ℕ, ‖(fderiv ℝ (e ∘ f ∘ e.symm) (e p)) ^ N‖ < 1) :
    PalisConjecture.IsAttractor n (f : M → M) {p} := by
  have hfix : ∀ k, (f : M → M)^[k] p = p := fun k => Function.iterate_fixed hp k
  refine ⟨by simp [hp], ⟨p, rfl, ?_⟩, ?_⟩
  · have : {y | ∃ k : ℕ, (f : M → M)^[k] p = y} = {p} := by
      ext y; simp [hfix, eq_comm]
    rw [this, closure_singleton]
  obtain ⟨N, hN⟩ := hsink
  set g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := e ∘ f ∘ e.symm with hgdef
  set x0 := e p
  have hx0 : x0 ∈ e.target := e.map_source hpe
  have hg0 : g x0 = x0 := by simp [hgdef, x0, e.left_inv hpe, hp]
  have hA := hasFDeriv_chart n r hr f p hp e he hpe
  set V : Set (EuclideanSpace ℝ (Fin n)) := e.target ∩ e.symm ⁻¹' ((f : M → M) ⁻¹' e.source) with hVdef
  have hVopen : IsOpen V := e.isOpen_inter_preimage_symm (e.open_source.preimage f.continuous)
  have hV : V ∈ 𝓝 x0 := hVopen.mem_nhds ⟨hx0, by simp [x0, e.left_inv hpe, hp, hpe]⟩
  obtain ⟨U, hU, hUprop⟩ := contract g x0 hg0 _ hA N hN V hV
  intro hnull
  have h0 := hnull e he
  have hsubset : U ⊆ e '' (PalisConjecture.basin (f : M → M) {p} ∩ e.source) := by
    intro x hx
    obtain ⟨horb, hconv⟩ := hUprop x hx
    have hxt : x ∈ e.target := (horb 0).1
    set q := e.symm x
    have hiter : ∀ k, (f : M → M)^[k] q = e.symm (g^[k] x) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        have hk := horb k
        simp only [hgdef, Function.comp_apply]
        rw [e.left_inv hk.2]
    have hq : Tendsto (fun k => (f : M → M)^[k] q) atTop (𝓝 p) := by
      have hc : Tendsto (fun k => e.symm (g^[k] x)) atTop (𝓝 (e.symm x0)) :=
        (e.continuousAt_symm hx0).tendsto.comp hconv
      rw [show e.symm x0 = p from e.left_inv hpe] at hc
      simpa [hiter] using hc
    refine ⟨q, ⟨omega_sub _ q p hq, e.map_target hxt⟩, e.right_inv hxt⟩
  have hpos : 0 < MeasureTheory.volume U := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    exact lt_of_lt_of_le (Metric.measure_ball_pos _ x0 hε) (MeasureTheory.measure_mono hball)
  have := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsubset
  rw [h0] at this
  exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl _)

end PalisSink
open PalisConjecture in
theorem solution (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : M ≃ₘ^(r : WithTop ℕ∞)⟮𝓡 n, 𝓡 n⟯ M) (p : M) (hp : f p = p)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (hpe : p ∈ e.source)
    (hsink : ∃ N : ℕ, ‖(fderiv ℝ (e ∘ f ∘ e.symm) (e p)) ^ N‖ < 1) :
    IsAttractor n (f : M → M) {p} :=
  PalisSink.sink n r hr f p hp e he hpe hsink
