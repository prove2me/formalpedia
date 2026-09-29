-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_unique_pareto_cell_cover_best
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T19:10:02.745375+00:00
-- url     : https://prove2.me/submissions/c3501a0e-0d03-4d23-b774-09b4643a933d

import Definitions.Def_PartialMonitoringGame
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Convex.Intrinsic

open scoped BigOperators
open Set Topology

namespace BanditAlgorithm

noncomputable section

variable {k d : ℕ} {𝕊 : Type*}

private lemma affineDim_stdSimplex_add_one (hd : 0 < d) :
    affineDim (stdSimplex ℝ (Fin d)) + 1 = d := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have heq : (fun i : Fin d ↦ Pi.single i (1 : ℝ)) = (Pi.basisFun ℝ (Fin d) : Fin d → Fin d → ℝ) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin d) i).symm
  have hli : LinearIndependent ℝ (fun i : Fin d ↦ Pi.single i (1 : ℝ)) := by
    rw [heq]
    exact (Pi.basisFun ℝ (Fin d)).linearIndependent
  have hai : AffineIndependent ℝ (fun i : Fin d ↦ Pi.single i (1 : ℝ)) :=
    hli.affineIndependent
  have hdim := hai.finrank_vectorSpan_add_one
  unfold affineDim
  rw [← convexHull_rangle_single_eq_stdSimplex ℝ (Fin d),
    affineSpan_convexHull, direction_affineSpan]
  simpa using hdim

private lemma nonempty_interior_of_nonempty_subtype_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s A : Set E} (hsconv : Convex ℝ s) (hsclosed : IsClosed s)
    (hsint : (interior s).Nonempty) (hAs : A ⊆ s)
    (hrel : (interior {x : s | (x : E) ∈ A}).Nonempty) :
    (interior A).Nonempty := by
  obtain ⟨x, hx⟩ := hrel
  have hopen : IsOpen (interior {x : s | (x : E) ∈ A}) := isOpen_interior
  rw [isOpen_induced_iff] at hopen
  obtain ⟨U, hUopen, hUeq⟩ := hopen
  have hxU : (x : E) ∈ U := by
    have : x ∈ Subtype.val ⁻¹' U := by simpa [hUeq] using hx
    exact this
  have hclosure : closure (interior s) = s := by
    rw [hsconv.closure_interior_eq_closure_of_nonempty_interior hsint,
      hsclosed.closure_eq]
  have hxcl : (x : E) ∈ closure (interior s) := by
    rw [hclosure]
    exact x.2
  obtain ⟨y, hyint, hyU⟩ := (mem_closure_iff.1 hxcl) U hUopen hxU
  refine ⟨y, interior_maximal ?_ (hUopen.inter isOpen_interior) ⟨hyint, hyU⟩⟩
  intro z hz
  have hzs : z ∈ s := interior_subset hz.2
  have hzrel : (⟨z, hzs⟩ : s) ∈ interior {x : s | (x : E) ∈ A} := by
    rw [← hUeq]
    exact hz.1
  have hzA : (⟨z, hzs⟩ : s) ∈ {x : s | (x : E) ∈ A} :=
    interior_subset hzrel
  exact hzA

private def cellInSimplex (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Set (stdSimplex ℝ (Fin d)) :=
  {u | (u : Fin d → ℝ) ∈ pmCell G a}

private lemma isClosed_cellInSimplex (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    IsClosed (cellInSimplex G a) := by
  rw [show cellInSimplex G a = {u : stdSimplex ℝ (Fin d) |
      ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * (u : Fin d → ℝ) i ≤ 0} by
    ext u
    change ((u : Fin d → ℝ) ∈ stdSimplex ℝ (Fin d) ∧
      ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * (u : Fin d → ℝ) i ≤ 0) ↔ _
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨u.2, h⟩]
  simp only [setOf_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_le
  · apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)
  · exact continuous_const

private lemma iUnion_cellInSimplex (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) :
    ⋃ a : Fin k, cellInSimplex G a = Set.univ := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  let vals : Finset ℝ := Finset.univ.image (fun a : Fin k ↦ ∑ i, G.L a i * (u : Fin d → ℝ) i)
  have hvals : vals.Nonempty := by
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
    let a : Fin k := Classical.choice inferInstance
    exact ⟨_, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let v := vals.min' hvals
  obtain ⟨a, hauniv, hav⟩ := Finset.mem_image.mp (vals.min'_mem hvals)
  refine ⟨a, ?_⟩
  change (u : Fin d → ℝ) ∈ stdSimplex ℝ (Fin d) ∧
    ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * (u : Fin d → ℝ) i ≤ 0
  refine ⟨u.2, ?_⟩
  intro b
  have hbmem : (∑ i, G.L b i * (u : Fin d → ℝ) i) ∈ vals :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hvle := vals.min'_le _ hbmem
  rw [← hav] at hvle
  have heq : (∑ i, (G.L a i - G.L b i) * (u : Fin d → ℝ) i) =
      (∑ i, G.L a i * (u : Fin d → ℝ) i) -
        ∑ i, G.L b i * (u : Fin d → ℝ) i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  linarith

private def simplexSpan (d : ℕ) : AffineSubspace ℝ (Fin d → ℝ) :=
  affineSpan ℝ (stdSimplex ℝ (Fin d))

private def simplexInSpan (d : ℕ) : Set (simplexSpan d) :=
  {u | (u : Fin d → ℝ) ∈ stdSimplex ℝ (Fin d)}

private def cellInSpan (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Set (simplexSpan d) :=
  {u | (u : Fin d → ℝ) ∈ pmCell G a}

private lemma isClosed_pmCell (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    IsClosed (pmCell G a) := by
  rw [show pmCell G a = stdSimplex ℝ (Fin d) ∩ {u : Fin d → ℝ |
      ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * (u : Fin d → ℝ) i ≤ 0} by
    ext u
    rfl]
  apply IsClosed.inter (isClosed_stdSimplex ℝ (Fin d))
  simp only [setOf_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_le
  · apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  · exact continuous_const

private lemma isClosed_cellInSpan (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    IsClosed (cellInSpan G a) := by
  exact (isClosed_pmCell G a).preimage continuous_subtype_val

private lemma sum_eq_one_of_mem_simplexSpan (u : simplexSpan d) :
    ∑ i, (u : Fin d → ℝ) i = 1 := by
  refine affineSpan_induction (k := ℝ) (p := fun v : Fin d → ℝ ↦ ∑ i, v i = 1)
    u.2 (fun x hx ↦ hx.2) ?_
  intro c x y z hx hy hz
  simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [Finset.sum_add_distrib]
  calc
    (∑ i, c • (x i - y i)) + ∑ i, z i =
        c * ((∑ i, x i) - ∑ i, y i) + ∑ i, z i := by
          simp_rw [smul_eq_mul]
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 1 := by rw [hx, hy, hz]; ring

private lemma full_cell_is_pareto
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d) (a : Fin k)
    (hfull : (interior (cellInSimplex G a)).Nonempty) :
    ParetoOptimalAction G a := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let u₀ : Fin d → ℝ := fun _ ↦ 1 / d
  have hu₀ : u₀ ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [u₀]
      positivity
    · simp [u₀, hd.ne']
  letI : Nonempty (simplexSpan d) :=
    ⟨⟨u₀, subset_affineSpan ℝ _ hu₀⟩⟩
  obtain ⟨x, hx⟩ := hfull
  have hopen : IsOpen (interior (cellInSimplex G a)) := isOpen_interior
  rw [isOpen_induced_iff] at hopen
  obtain ⟨U, hUopen, hUeq⟩ := hopen
  have hxU : (x : Fin d → ℝ) ∈ U := by
    have : x ∈ Subtype.val ⁻¹' U := by simpa [hUeq] using hx
    exact this
  let F : ℝ → (Fin d → ℝ) := fun t ↦ (1 - t) • (x : Fin d → ℝ) + t • u₀
  have hFcont : Continuous F := by
    fun_prop
  have hFzero : F 0 = (x : Fin d → ℝ) := by
    simp [F]
  have hFU : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), F t ∈ U := by
    apply (hFcont.continuousAt.mono_left inf_le_left).eventually
    rw [hFzero]
    exact hUopen.mem_nhds hxU
  have hFlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hFpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  obtain ⟨t, htU, htlt, htpos⟩ := Filter.Eventually.exists
    (hFU.and (hFlt.and hFpos))
  have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr htlt.le
  have ht1 : 0 ≤ t := htpos.le
  have htsum : (1 - t) + t = 1 := by ring
  have hFsimplex : F t ∈ stdSimplex ℝ (Fin d) := by
    exact (convex_stdSimplex ℝ (Fin d)) x.2 hu₀ ht0 ht1 htsum
  have hFstrict : ∀ i, 0 < F t i := by
    intro i
    dsimp [F, u₀]
    have hxnonneg := x.2.1 i
    have hudpos : 0 < (1 : ℝ) / d := by positivity
    have hfirst : 0 ≤ (1 - t) * (x : Fin d → ℝ) i := mul_nonneg ht0 hxnonneg
    have hsecond : 0 < t * ((1 : ℝ) / d) := mul_pos htpos hudpos
    exact add_pos_of_nonneg_of_pos hfirst hsecond
  let y : simplexSpan d := ⟨F t, subset_affineSpan ℝ _ hFsimplex⟩
  let W : Set (simplexSpan d) :=
    {z | (z : Fin d → ℝ) ∈ U ∧ ∀ i, 0 < (z : Fin d → ℝ) i}
  have hWopen : IsOpen W := by
    apply hUopen.preimage continuous_subtype_val |>.inter
    have ho : IsOpen (⋂ i, {z : simplexSpan d | 0 < (z : Fin d → ℝ) i}) := by
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
    convert ho using 1
    ext z
    constructor
    · intro hz
      exact Set.mem_iInter.mpr hz
    · intro hz
      exact Set.mem_iInter.mp hz
  have hyW : y ∈ W := by
    exact ⟨htU, hFstrict⟩
  have hWsub : W ⊆ cellInSpan G a := by
    intro z hz
    have hzsimplex : (z : Fin d → ℝ) ∈ stdSimplex ℝ (Fin d) := by
      constructor
      · exact fun i ↦ (hz.2 i).le
      · exact sum_eq_one_of_mem_simplexSpan z
    let zs : stdSimplex ℝ (Fin d) := ⟨z, hzsimplex⟩
    have hzrel : zs ∈ interior (cellInSimplex G a) := by
      rw [← hUeq]
      exact hz.1
    have hzc := interior_subset hzrel
    change (z : Fin d → ℝ) ∈ pmCell G a at hzc
    exact hzc
  have hspanW : affineSpan ℝ W = ⊤ := hWopen.affineSpan_eq_top ⟨y, hyW⟩
  have hspanCellH : affineSpan ℝ (cellInSpan G a) = ⊤ := by
    apply top_unique
    rw [← hspanW]
    exact affineSpan_mono ℝ hWsub
  have himage : (simplexSpan d).subtype '' cellInSpan G a = pmCell G a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      refine ⟨⟨z, subset_affineSpan ℝ _ hz.1⟩, hz, rfl⟩
  have hmap := AffineSubspace.map_span (simplexSpan d).subtype (cellInSpan G a)
  rw [himage, hspanCellH] at hmap
  have htopmap : (⊤ : AffineSubspace ℝ (simplexSpan d)).map
      (simplexSpan d).subtype = simplexSpan d := by
    ext z
    simp only [AffineSubspace.mem_map, AffineSubspace.mem_top, true_and]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have hspanAmbient : affineSpan ℝ (pmCell G a) = simplexSpan d := by
    rw [← hmap]
    exact htopmap
  have hxc := interior_subset hx
  change (x : Fin d → ℝ) ∈ pmCell G a at hxc
  refine ⟨⟨x, hxc⟩, ?_⟩
  unfold affineDim
  rw [hspanAmbient]
  exact affineDim_stdSimplex_add_one hd

theorem test_dense_full_cells
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    Dense (⋃ a : Fin k, interior (cellInSimplex G a)) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let u₀ : Fin d → ℝ := fun _ ↦ 1 / d
  have hu₀ : u₀ ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [u₀]
      positivity
    · simp [u₀, hd.ne']
  letI : Nonempty (stdSimplex ℝ (Fin d)) := ⟨⟨u₀, hu₀⟩⟩
  letI : CompactSpace (stdSimplex ℝ (Fin d)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  letI : CompleteSpace (stdSimplex ℝ (Fin d)) :=
    (isClosed_stdSimplex ℝ (Fin d)).completeSpace_coe
  apply dense_iUnion_interior_of_closed
  · exact isClosed_cellInSimplex G
  · exact iUnion_cellInSimplex G hk

theorem test_every_point_in_full_cell
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d)
    (u : stdSimplex ℝ (Fin d)) :
    ∃ a : Fin k, u ∈ cellInSimplex G a ∧
      (interior (cellInSimplex G a)).Nonempty := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let u₀ : Fin d → ℝ := fun _ ↦ 1 / d
  have hu₀ : u₀ ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [u₀]
      positivity
    · simp [u₀, hd.ne']
  letI : Nonempty (stdSimplex ℝ (Fin d)) := ⟨⟨u₀, hu₀⟩⟩
  letI : CompleteSpace (stdSimplex ℝ (Fin d)) :=
    (isClosed_stdSimplex ℝ (Fin d)).completeSpace_coe
  have hdense := test_dense_full_cells G hk hd
  have hucl : u ∈ closure (⋃ a : Fin k, interior (cellInSimplex G a)) := by
    rw [hdense.closure_eq]
    exact Set.mem_univ u
  rw [closure_iUnion_of_finite] at hucl
  obtain ⟨a, hua⟩ := Set.mem_iUnion.mp hucl
  have hnonempty : (interior (cellInSimplex G a)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, closure_empty] at hua
    exact hua
  refine ⟨a, ?_, hnonempty⟩
  exact closure_minimal interior_subset (isClosed_cellInSimplex G a) hua

private lemma exists_full_best_finite_sequence
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d)
    (n : ℕ) (out : Fin n → Fin d) :
    ∃ b : Fin k, (interior (cellInSimplex G b)).Nonempty ∧
      ∀ a : Fin k, ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t) := by
  classical
  by_cases hn : n = 0
  · subst n
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
    let u₀ : Fin d → ℝ := fun _ ↦ 1 / d
    have hu₀ : u₀ ∈ stdSimplex ℝ (Fin d) := by
      constructor
      · intro i
        dsimp [u₀]
        positivity
      · simp [u₀, hd.ne']
    obtain ⟨b, hbcell, hbfull⟩ := test_every_point_in_full_cell G hk hd ⟨u₀, hu₀⟩
    refine ⟨b, hbfull, ?_⟩
    intro a
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let lam : Fin d → ℝ := fun j ↦
      (1 / (n : ℝ)) * ∑ t : Fin n, if out t = j then (1 : ℝ) else 0
    have hlam : lam ∈ stdSimplex ℝ (Fin d) := by
      constructor
      · intro j
        dsimp [lam]
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg fun t ht ↦ by split <;> positivity
      · dsimp [lam]
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp [hn]
    obtain ⟨b, hbcell, hbfull⟩ := test_every_point_in_full_cell G hk hd ⟨lam, hlam⟩
    refine ⟨b, hbfull, ?_⟩
    intro a
    have hba := hbcell.2 a
    have hdot (c : Fin k) :
        (∑ j, G.L c j * lam j) = (1 / (n : ℝ)) * ∑ t, G.L c (out t) := by
      dsimp [lam]
      calc
        ∑ j, G.L c j * ((1 / (n : ℝ)) *
            ∑ t, if out t = j then (1 : ℝ) else 0) =
            (1 / (n : ℝ)) * ∑ j, G.L c j *
              (∑ t, if out t = j then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = (1 / (n : ℝ)) * ∑ t, G.L c (out t) := by
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          simp
    have hscaled : (1 / (n : ℝ)) * ∑ t, G.L b (out t) ≤
        (1 / (n : ℝ)) * ∑ t, G.L a (out t) := by
      have heq : (∑ j, (G.L b j - G.L a j) * lam j) =
          (∑ j, G.L b j * lam j) - ∑ j, G.L a j * lam j := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      change (∑ j, (G.L b j - G.L a j) * lam j) ≤ 0 at hba
      rw [heq, hdot b, hdot a] at hba
      linarith
    have hinvpos : 0 < (1 / (n : ℝ)) := by positivity
    nlinarith

theorem test_pareto_cover_best
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, ParetoOptimalAction G a) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) := by
  classical
  let S := Finset.univ.filter fun a : Fin k ↦
    (interior (cellInSimplex G a)).Nonempty
  obtain ⟨b₀, hb₀full, hb₀best⟩ := exists_full_best_finite_sequence G hk hd 0 Fin.elim0
  refine ⟨S, ⟨b₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₀full⟩⟩, ?_, ?_⟩
  · intro a ha
    exact full_cell_is_pareto G hd a (Finset.mem_filter.mp ha).2
  · intro n out
    obtain ⟨b, hbfull, hbbest⟩ := exists_full_best_finite_sequence G hk hd n out
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbfull⟩, hbbest⟩

theorem test_unique_pareto_cover_best
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, ParetoOptimalAction G a) ∧
      (∀ a ∈ S, ∀ b ∈ S, (∀ i, G.L a i = G.L b i) → a = b) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) := by
  classical
  let Full : Fin k → Prop := fun a ↦ (interior (cellInSimplex G a)).Nonempty
  let P : Finset (Fin k) := Finset.univ.filter Full
  have hPmem {a : Fin k} (ha : Full a) : a ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  let cls (a : Fin k) : Finset (Fin k) := P.filter fun b ↦ ∀ i, G.L b i = G.L a i
  have hcls {a : Fin k} (ha : Full a) : (cls a).Nonempty := by
    refine ⟨a, Finset.mem_filter.mpr ⟨hPmem ha, fun i ↦ rfl⟩⟩
  let rep (a : Fin k) : Fin k := if ha : Full a then (cls a).min' (hcls ha) else a
  have hrep_mem {a : Fin k} (ha : Full a) : rep a ∈ P := by
    simp only [rep, dif_pos ha]
    exact (Finset.mem_filter.mp ((cls a).min'_mem (hcls ha))).1
  have hrep_full {a : Fin k} (ha : Full a) : Full (rep a) :=
    (Finset.mem_filter.mp (hrep_mem ha)).2
  have hrep_loss {a : Fin k} (ha : Full a) : ∀ i, G.L (rep a) i = G.L a i := by
    simp only [rep, dif_pos ha]
    exact (Finset.mem_filter.mp ((cls a).min'_mem (hcls ha))).2
  let S : Finset (Fin k) := P.image rep
  obtain ⟨a₀, ha₀full, ha₀best⟩ := exists_full_best_finite_sequence G hk hd 0 Fin.elim0
  have ha₀P : a₀ ∈ P := hPmem ha₀full
  have hSne : S.Nonempty := ⟨rep a₀, Finset.mem_image.mpr ⟨a₀, ha₀P, rfl⟩⟩
  refine ⟨S, hSne, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hr
    exact full_cell_is_pareto G hd _ (hrep_full (Finset.mem_filter.mp haP).2)
  · intro r hr s hs hrs
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hbP, rfl⟩ := Finset.mem_image.mp hs
    have ha : Full a := (Finset.mem_filter.mp haP).2
    have hb : Full b := (Finset.mem_filter.mp hbP).2
    have hab : ∀ i, G.L a i = G.L b i := by
      intro i
      rw [← hrep_loss ha i, hrs i, hrep_loss hb i]
    simp only [rep, dif_pos ha, dif_pos hb]
    congr 1
    ext c
    simp only [cls, Finset.mem_filter]
    constructor
    · rintro ⟨hcP, hca⟩
      exact ⟨hcP, fun i ↦ (hca i).trans (hab i)⟩
    · rintro ⟨hcP, hcb⟩
      exact ⟨hcP, fun i ↦ (hcb i).trans (hab i).symm⟩
  · intro n out
    obtain ⟨a, hafull, habest⟩ := exists_full_best_finite_sequence G hk hd n out
    refine ⟨rep a, Finset.mem_image.mpr ⟨a, hPmem hafull, rfl⟩, ?_⟩
    intro b
    calc
      ∑ t, G.L (rep a) (out t) = ∑ t, G.L a (out t) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hrep_loss hafull (out t)
      _ ≤ ∑ t, G.L b (out t) := habest b

theorem test_unique_pareto_cell_cover_best
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, ParetoOptimalAction G a) ∧
      (∀ a ∈ S, ∀ b ∈ S, (∀ i, G.L a i = G.L b i) → a = b) ∧
      (∀ u, u ∈ stdSimplex ℝ (Fin d) → ∃ a ∈ S, u ∈ pmCell G a) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) := by
  classical
  let Full : Fin k → Prop := fun a ↦ (interior (cellInSimplex G a)).Nonempty
  let P : Finset (Fin k) := Finset.univ.filter Full
  have hPmem {a : Fin k} (ha : Full a) : a ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  let cls (a : Fin k) : Finset (Fin k) := P.filter fun b ↦ ∀ i, G.L b i = G.L a i
  have hcls {a : Fin k} (ha : Full a) : (cls a).Nonempty := by
    refine ⟨a, Finset.mem_filter.mpr ⟨hPmem ha, fun i ↦ rfl⟩⟩
  let rep (a : Fin k) : Fin k := if ha : Full a then (cls a).min' (hcls ha) else a
  have hrep_mem {a : Fin k} (ha : Full a) : rep a ∈ P := by
    simp only [rep, dif_pos ha]
    exact (Finset.mem_filter.mp ((cls a).min'_mem (hcls ha))).1
  have hrep_full {a : Fin k} (ha : Full a) : Full (rep a) :=
    (Finset.mem_filter.mp (hrep_mem ha)).2
  have hrep_loss {a : Fin k} (ha : Full a) : ∀ i, G.L (rep a) i = G.L a i := by
    simp only [rep, dif_pos ha]
    exact (Finset.mem_filter.mp ((cls a).min'_mem (hcls ha))).2
  have hrep_cell {a : Fin k} (ha : Full a) : pmCell G (rep a) = pmCell G a := by
    ext u
    simp only [pmCell, Set.mem_setOf_eq]
    constructor <;> rintro ⟨hu, hopt⟩ <;> refine ⟨hu, ?_⟩ <;> intro b
    · simpa only [hrep_loss ha] using hopt b
    · simpa only [hrep_loss ha] using hopt b
  let S : Finset (Fin k) := P.image rep
  obtain ⟨a₀, ha₀full, ha₀best⟩ := exists_full_best_finite_sequence G hk hd 0 Fin.elim0
  have ha₀P : a₀ ∈ P := hPmem ha₀full
  have hSne : S.Nonempty := ⟨rep a₀, Finset.mem_image.mpr ⟨a₀, ha₀P, rfl⟩⟩
  refine ⟨S, hSne, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hr
    exact full_cell_is_pareto G hd _ (hrep_full (Finset.mem_filter.mp haP).2)
  · intro r hr s hs hrs
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b, hbP, rfl⟩ := Finset.mem_image.mp hs
    have ha : Full a := (Finset.mem_filter.mp haP).2
    have hb : Full b := (Finset.mem_filter.mp hbP).2
    have hab : ∀ i, G.L a i = G.L b i := by
      intro i
      rw [← hrep_loss ha i, hrs i, hrep_loss hb i]
    simp only [rep, dif_pos ha, dif_pos hb]
    congr 1
    ext c
    simp only [cls, Finset.mem_filter]
    constructor
    · rintro ⟨hcP, hca⟩
      exact ⟨hcP, fun i ↦ (hca i).trans (hab i)⟩
    · rintro ⟨hcP, hcb⟩
      exact ⟨hcP, fun i ↦ (hcb i).trans (hab i).symm⟩
  · intro u hu
    obtain ⟨a, hacell, hafull⟩ :=
      test_every_point_in_full_cell G hk hd ⟨u, hu⟩
    refine ⟨rep a, Finset.mem_image.mpr ⟨a, hPmem hafull, rfl⟩, ?_⟩
    rw [hrep_cell hafull]
    exact hacell
  · intro n out
    obtain ⟨a, hafull, habest⟩ := exists_full_best_finite_sequence G hk hd n out
    refine ⟨rep a, Finset.mem_image.mpr ⟨a, hPmem hafull, rfl⟩, ?_⟩
    intro b
    calc
      ∑ t, G.L (rep a) (out t) = ∑ t, G.L a (out t) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hrep_loss hafull (out t)
      _ ≤ ∑ t, G.L b (out t) := habest b

end
end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hk : 0 < k) (hd : 0 < d) :
    ∃ S : Finset (Fin k), S.Nonempty ∧
      (∀ a ∈ S, BanditAlgorithm.ParetoOptimalAction G a) ∧
      (∀ a ∈ S, ∀ b ∈ S, (∀ i, G.L a i = G.L b i) → a = b) ∧
      (∀ u, u ∈ stdSimplex ℝ (Fin d) →
        ∃ a ∈ S, u ∈ BanditAlgorithm.pmCell G a) ∧
      (∀ (n : ℕ) (out : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (out t) ≤ ∑ t, G.L a (out t)) :=
  BanditAlgorithm.test_unique_pareto_cell_cover_best G hk hd
