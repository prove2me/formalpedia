-- Prove2me | solution 1 for KServer.wfaU_trees_three_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:16:56.506774+00:00
-- url     : https://prove2.me/submissions/531c888c-aa52-46d0-a618-29b6ad3a1184

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_wfaU
import Definitions.Def_KServer_tree_metric
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Theorems.Thm_KServer_wfaU_potential_criterion_univ
import Theorems.Thm_KServer_workFnU_isometry_equivariant
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict
import Theorems.Thm_KServer_workFnU_growth_le_antipode
import Theorems.Thm_KServer_workFnU_mono
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_tree_anchor_at_request

open KServer

/-- Competitiveness transfers along a bijective isometry to a `Type`-level model, where
the whole Coester–Koutsoupias potential machinery is available. -/
private theorem competitive_of_model (M : Type*) [MetricSpace M] [Fintype M]
    (N : Type) [MetricSpace N] [Fintype N]
    (e : M ≃ N) (he : ∀ x y : M, dist (e x) (e y) = dist x y)
    (hMN : IsTreeVertexSpace N) (C₀ : Config 3 M) :
    IsCompetitive (WFAU (Nat.succ_pos 2) C₀) 3 := by
  classical
  haveI hNeM : Nonempty M := ⟨C₀ 0⟩
  haveI hNeN : Nonempty N := ⟨e (C₀ 0)⟩
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have hsymm : ∀ a b : N, dist (e.symm a) (e.symm b) = dist a b := by
    intro a b
    have h := he (e.symm a) (e.symm b)
    rw [e.apply_symm_apply, e.apply_symm_apply] at h
    exact h.symm
  -- a positive uniform bound on the distances of M (hence of N)
  obtain ⟨Δ, hΔ0, hΔ⟩ : ∃ Δ : ℝ, 0 < Δ ∧ ∀ u v : M, dist u v ≤ Δ := by
    have hne : (Finset.univ : Finset (M × M)).Nonempty := Finset.univ_nonempty
    refine ⟨(Finset.univ.sup' hne fun p : M × M => dist p.1 p.2) + 1, ?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ Finset.univ.sup' hne fun p : M × M => dist p.1 p.2 := by
        have h := Finset.le_sup' (fun p : M × M => dist p.1 p.2)
          (Finset.mem_univ (C₀ 0, C₀ 0))
        simpa using h
      linarith
    · intro u v
      have h : dist u v ≤ Finset.univ.sup' hne fun p : M × M => dist p.1 p.2 :=
        Finset.le_sup' (fun p : M × M => dist p.1 p.2) (Finset.mem_univ (u, v))
      linarith
  have hΔN : ∀ a b : N, dist a b ≤ Δ := by
    intro a b
    rw [← hsymm a b]
    exact hΔ _ _
  -- the antipodal extension of the model
  letI : MetricSpace (N ⊕ N) := antipodalExtension N Δ hΔ0 hΔN
  have dLL : ∀ a b : N, dist (Sum.inl a : N ⊕ N) (Sum.inl b) = dist a b := fun _ _ => rfl
  have dLR : ∀ a b : N, dist (Sum.inl a : N ⊕ N) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have dRL : ∀ a b : N, dist (Sum.inr a : N ⊕ N) (Sum.inl b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have dRR : ∀ a b : N, dist (Sum.inr a : N ⊕ N) (Sum.inr b) = dist a b := fun _ _ => rfl
  have hb2 : ∀ u v : N ⊕ N, dist u v ≤ 2 * Δ := fun u v => antiD_le N Δ hΔ0 hΔN u v
  -- transport of the work function to the model and its extension
  have h1 : ∀ (τ : List M) (X : Config 3 M),
      workFnU C₀ τ X
        = workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
            ((τ.map ⇑e).map Sum.inl) (fun i => Sum.inl (e (X i))) := by
    intro τ X
    exact ((workFnU_antipodal_extension_restrict 3 h3 N Δ hΔ0 hΔN (fun i => e (C₀ i))
        (τ.map ⇑e) (fun i => e (X i))).trans
      (workFnU_isometry_equivariant 3 M N e he C₀ τ X)).symm
  refine wfaU_potential_criterion_univ 3 (Nat.succ_pos 2) M C₀ 3 (by norm_num)
    (fun τ => 24 * Δ - ckPot N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e)) ?_ ?_
  · -- the offset property
    intro τ X
    show 0 ≤ 24 * Δ - ckPot N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e)
      + (3 + 1) * workFnU C₀ τ X
    have hlip : ∀ P : Config 3 (N ⊕ N),
        workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl) P
          ≤ workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl)
              (fun i => Sum.inl (e (X i))) + 6 * Δ := by
      intro P
      have h := workFnU_lipschitz 3 h3 (N ⊕ N) (fun i => Sum.inl (e (C₀ i)))
        ((τ.map ⇑e).map Sum.inl) P (fun i => Sum.inl (e (X i)))
      have hmc : moveCost (fun i => Sum.inl (e (X i)) : Config 3 (N ⊕ N)) P ≤ 6 * Δ := by
        unfold moveCost
        rw [Fin.sum_univ_three]
        have b0 := hb2 (Sum.inl (e (X 0))) (P 0)
        have b1 := hb2 (Sum.inl (e (X 1))) (P 1)
        have b2 := hb2 (Sum.inl (e (X 2))) (P 2)
        show dist (Sum.inl (e (X 0)) : N ⊕ N) (P 0) + dist (Sum.inl (e (X 1))) (P 1)
            + dist (Sum.inl (e (X 2))) (P 2) ≤ 6 * Δ
        linarith
      linarith
    have hle := ckPot_le N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e)
      (e (C₀ 0)) (e (C₀ 0)) (e (C₀ 0))
    have hAt0 : ckPotAt N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e)
          (e (C₀ 0)) (e (C₀ 0)) (e (C₀ 0))
        = workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl)
            ![Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0))]
          + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl)
              ![Sum.inr (e (C₀ 0)), Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0))]
          + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl)
              ![Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0)), Sum.inl (e (C₀ 0))]
          + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl)
              ![Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0))] := rfl
    rw [hAt0] at hle
    rw [h1 τ X]
    linarith [hlip ![Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0))],
      hlip ![Sum.inr (e (C₀ 0)), Sum.inl (e (C₀ 0)), Sum.inl (e (C₀ 0))],
      hlip ![Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0)), Sum.inl (e (C₀ 0))],
      hlip ![Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0)), Sum.inr (e (C₀ 0))]]
  · -- the update property
    intro τ s X
    show workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X
      + ((24 * Δ - ckPot N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e))
        - (24 * Δ - ckPot N Δ hΔ0 hΔN (fun i => e (C₀ i)) ((τ ++ [s]).map ⇑e)))
    have hmap2 : (τ ++ [s]).map ⇑e = τ.map ⇑e ++ [e s] := by simp
    have hml : (τ.map ⇑e).map (Sum.inl : N → N ⊕ N) ++ [Sum.inl (e s)]
        = (τ.map ⇑e ++ [e s]).map Sum.inl := by simp
    -- the appended-request form of the transport
    have h2 : workFnU C₀ (τ ++ [s]) X
        = workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
            ((τ.map ⇑e ++ [e s]).map Sum.inl) (fun i => Sum.inl (e (X i))) := by
      rw [h1 (τ ++ [s]) X, hmap2]
    -- the growth at any configuration is at most the growth at the antipode of the request
    have hanti : ∀ y : N ⊕ N, dist y (Sum.inl (e s)) + dist y (Sum.inr (e s)) = 2 * Δ := by
      intro y
      rcases y with a | a
      · rw [dLL, dLR]; ring
      · rw [dRL, dRR]; ring
    have hgrow :
        workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
            ((τ.map ⇑e ++ [e s]).map Sum.inl) (fun i => Sum.inl (e (X i)))
          - workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
              ((τ.map ⇑e).map Sum.inl) (fun i => Sum.inl (e (X i)))
        ≤ workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
            ((τ.map ⇑e ++ [e s]).map Sum.inl) (fun _ => Sum.inr (e s))
          - workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
              ((τ.map ⇑e).map Sum.inl) (fun _ => Sum.inr (e s)) := by
      rw [← hml]
      exact workFnU_growth_le_antipode 3 h3 (N ⊕ N) (fun i => Sum.inl (e (C₀ i)))
        ((τ.map ⇑e).map Sum.inl) (Sum.inl (e s)) (Sum.inr (e s)) Δ hanti
        (fun i => Sum.inl (e (X i)))
    -- monotonicity of the extension work function
    have hmono : ∀ P : Config 3 (N ⊕ N),
        workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) ((τ.map ⇑e).map Sum.inl) P
          ≤ workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N))
              ((τ.map ⇑e ++ [e s]).map Sum.inl) P := by
      intro P
      rw [← hml]
      exact workFnU_mono 3 h3 (N ⊕ N) (fun i => Sum.inl (e (C₀ i)))
        ((τ.map ⇑e).map Sum.inl) (Sum.inl (e s)) P
    -- the anchoring theorem places the new minimum at the request
    obtain ⟨y, z, hyz⟩ := tree_anchor_at_request N hMN Δ hΔ0 hΔN (fun i => e (C₀ i))
      (τ.map ⇑e) (e s)
    have hle := ckPot_le N Δ hΔ0 hΔN (fun i => e (C₀ i)) (τ.map ⇑e) y z (e s)
    have hvec : (fun _ : Fin 3 => (Sum.inr (e s) : N ⊕ N))
        = ![Sum.inr (e s), Sum.inr (e s), Sum.inr (e s)] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    have hAt : ∀ σ'' : List N,
        ckPotAt N Δ hΔ0 hΔN (fun i => e (C₀ i)) σ'' y z (e s)
          = workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) (σ''.map Sum.inl)
              ![Sum.inl y, Sum.inl z, Sum.inl (e s)]
            + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) (σ''.map Sum.inl)
                ![Sum.inr y, Sum.inl z, Sum.inl (e s)]
            + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) (σ''.map Sum.inl)
                ![Sum.inr z, Sum.inr z, Sum.inl (e s)]
            + workFnU (fun i => Sum.inl (e (C₀ i)) : Config 3 (N ⊕ N)) (σ''.map Sum.inl)
                (fun _ => Sum.inr (e s)) := by
      intro σ''
      rw [hvec]
      rfl
    rw [hAt (τ.map ⇑e ++ [e s])] at hyz
    rw [hAt (τ.map ⇑e)] at hle
    rw [hmap2, h1 τ X, h2]
    linarith [hgrow, hyz, hle,
      hmono ![Sum.inl y, Sum.inl z, Sum.inl (e s)],
      hmono ![Sum.inr y, Sum.inl z, Sum.inl (e s)],
      hmono ![Sum.inr z, Sum.inr z, Sum.inl (e s)]]

/-- **The k-server conjecture for k = 3 on trees, for the unlabelled Work Function
Algorithm** (Coester–Koutsoupias): on the vertex set of any finite weighted tree, WFAU
is 3-competitive. -/
theorem solution {M : Type*} [MetricSpace M] [Fintype M]
    (hM : IsTreeVertexSpace M) (C₀ : Config 3 M) :
    IsCompetitive (WFAU (Nat.succ_pos 2) C₀) 3 := by
  classical
  haveI hNeM : Nonempty M := ⟨C₀ 0⟩
  set e : M ≃ Fin (Fintype.card M) := Fintype.equivFin M with he_def
  letI : MetricSpace (Fin (Fintype.card M)) :=
    MetricSpace.induced (⇑e.symm) e.symm.injective inferInstance
  have he : ∀ x y : M, dist (e x) (e y) = dist x y := by
    intro x y
    show dist (e.symm (e x)) (e.symm (e y)) = dist x y
    rw [e.symm_apply_apply, e.symm_apply_apply]
  have hMN : IsTreeVertexSpace (Fin (Fintype.card M)) := by
    obtain ⟨G, hG, w, hw⟩ := hM
    refine ⟨G.comap ⇑e.symm.toEmbedding, ?_, fun a b => w (e.symm a) (e.symm b), ?_⟩
    · exact (SimpleGraph.Iso.comap e.symm G).isTree_iff.mpr hG
    · intro u v p
      have hp' : (SimpleGraph.Walk.map (SimpleGraph.Hom.comap (⇑e.symm.toEmbedding) G)
          (p : (G.comap ⇑e.symm.toEmbedding).Walk u v)).IsPath :=
        SimpleGraph.Walk.map_isPath_of_injective (fun a b h => e.symm.injective h) p.2
      have hw' := hw (e.symm u) (e.symm v)
        ⟨SimpleGraph.Walk.map (SimpleGraph.Hom.comap (⇑e.symm.toEmbedding) G)
          (p : (G.comap ⇑e.symm.toEmbedding).Walk u v), hp'⟩
      have hdist : dist u v = dist (e.symm u) (e.symm v) := rfl
      rw [hdist, hw']
      unfold walkWeight
      show (List.map (fun d => w d.toProd.1 d.toProd.2)
          (SimpleGraph.Walk.map (SimpleGraph.Hom.comap (⇑e.symm.toEmbedding) G)
            (p : (G.comap ⇑e.symm.toEmbedding).Walk u v)).darts).sum
        = (List.map (fun d => w (e.symm d.toProd.1) (e.symm d.toProd.2))
            ((p : (G.comap ⇑e.symm.toEmbedding).Walk u v)).darts).sum
      rw [SimpleGraph.Walk.darts_map, List.map_map]
      rfl
  exact competitive_of_model M (Fin (Fintype.card M)) e he hMN C₀
