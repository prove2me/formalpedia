-- Prove2me | solution 2 for EmergentGeometry.no_bulk_geometry_realises_Sw
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:16:35.028084+00:00
-- url     : https://prove2.me/submissions/94c9e4fe-9c46-420a-8a3a-ff8035cd7398

import Mathlib
import Definitions.Def_Novelty_CyclicIndependence
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicCyclicInequality
open EmergentGeometry Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (M : HoloModel V)
    (A₀ A₁ A₂ A₃ A₄ : Region V)
    (hd : ∀ v, AtMostOneTrue (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v))
    (hreal : ∀ b₀ b₁ b₂ b₃ b₄ : Bool,
      entropy M (unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄) = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ)) :
    False := by
  have hcyc : entropy M (fun v => A₀ v || A₁ v) + entropy M (fun v => A₁ v || A₂ v)
        + entropy M (fun v => A₂ v || A₃ v) + entropy M (fun v => A₃ v || A₄ v)
        + entropy M (fun v => A₄ v || A₀ v)
        + entropy M (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
      ≤ entropy M (fun v => A₀ v || A₁ v || A₂ v)
        + entropy M (fun v => A₁ v || A₂ v || A₃ v)
        + entropy M (fun v => A₂ v || A₃ v || A₄ v)
        + entropy M (fun v => A₃ v || A₄ v || A₀ v)
        + entropy M (fun v => A₄ v || A₀ v || A₁ v) := by
    have hcut : ∀ f₀ f₁ f₂ f₃ f₄ : Region V,
        cutWeight M.toBulkGraph (fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
          + cutWeight M.toBulkGraph (fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v))
          + cutWeight M.toBulkGraph (fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v))
          + cutWeight M.toBulkGraph (fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v))
          + cutWeight M.toBulkGraph (fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v))
          + cutWeight M.toBulkGraph (fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v)
          ≤ cutWeight M.toBulkGraph f₀ + cutWeight M.toBulkGraph f₁ + cutWeight M.toBulkGraph f₂
            + cutWeight M.toBulkGraph f₃ + cutWeight M.toBulkGraph f₄ := by
      intro f₀ f₁ f₂ f₃ f₄
      have hcomb : ∀ {m n : ℕ} (F : Fin m → Region V) (H : Fin n → Region V),
          (∀ u v : V, M.toBulkGraph.weight u v ≠ 0 →
            ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) →
          ∑ i, cutWeight M.toBulkGraph (H i) ≤ ∑ j, cutWeight M.toBulkGraph (F j) := by
        intro m n F H h
        -- pointwise comparison of the weighted separation counts
        have hpt : ∀ u v : V,
            ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v
              ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
          intro u v
          by_cases hw : M.toBulkGraph.weight u v = 0
          · simp [hw]
          · have hle : ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ)
                ≤ ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) := by
              exact_mod_cast h u v hw
            exact mul_le_mul_of_nonneg_right hle (M.toBulkGraph.weight_nonneg u v)
        -- collect each family into a single double sum
        have hcollect : ∀ {k : ℕ} (K : Fin k → Region V),
            (∑ i, cutWeight M.toBulkGraph (K i))
              = (∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v) / 2 := by
          intro k K
          simp only [cutWeight]
          rw [← Finset.sum_div]
          congr 1
          calc (∑ i, ∑ u : V, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v)
              = ∑ u : V, ∑ i, ∑ v : V, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
                Finset.sum_comm
            _ = ∑ u : V, ∑ v : V, ∑ i, (sepBit (K i u) (K i v) : ℝ) * M.toBulkGraph.weight u v :=
                Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
            _ = ∑ u : V, ∑ v : V, ((∑ i, sepBit (K i u) (K i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v := by
                refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
                push_cast
                rw [Finset.sum_mul]
        rw [hcollect H, hcollect F]
        have hsum : (∑ u : V, ∑ v : V, ((∑ i, sepBit (H i u) (H i v) : ℕ) : ℝ) * M.toBulkGraph.weight u v)
            ≤ ∑ u : V, ∑ v : V, ((∑ j, sepBit (F j u) (F j v) : ℕ) : ℝ) * M.toBulkGraph.weight u v :=
          Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpt u v))
        linarith
      have hbool : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
          sepBit (cyc a0 a1 a2 a3 a4) (cyc b0 b1 b2 b3 b4)
            + sepBit (cyc a1 a2 a3 a4 a0) (cyc b1 b2 b3 b4 b0)
            + sepBit (cyc a2 a3 a4 a0 a1) (cyc b2 b3 b4 b0 b1)
            + sepBit (cyc a3 a4 a0 a1 a2) (cyc b3 b4 b0 b1 b2)
            + sepBit (cyc a4 a0 a1 a2 a3) (cyc b4 b0 b1 b2 b3)
            + sepBit (a0 || a1 || a2 || a3 || a4) (b0 || b1 || b2 || b3 || b4)
          ≤ sepBit a0 b0 + sepBit a1 b1 + sepBit a2 b2 + sepBit a3 b3 + sepBit a4 b4 := by
        decide
      have key := hcomb ![f₀, f₁, f₂, f₃, f₄]
        ![fun v => cyc (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v),
          fun v => cyc (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₀ v),
          fun v => cyc (f₂ v) (f₃ v) (f₄ v) (f₀ v) (f₁ v),
          fun v => cyc (f₃ v) (f₄ v) (f₀ v) (f₁ v) (f₂ v),
          fun v => cyc (f₄ v) (f₀ v) (f₁ v) (f₂ v) (f₃ v),
          fun v => f₀ v || f₁ v || f₂ v || f₃ v || f₄ v]
        (by
          intro u v _
          simp only [Fin.sum_univ_six, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
            Matrix.tail_cons, Matrix.cons_val_fin_one, Matrix.cons_val_succ]
          exact hbool (f₀ u) (f₁ u) (f₂ u) (f₃ u) (f₄ u) (f₀ v) (f₁ v) (f₂ v) (f₃ v) (f₄ v))
      simpa [Fin.sum_univ_six, Fin.sum_univ_five, add_assoc] using key
    have hpair : ∀ a0 a1 a2 a3 a4 : Bool, AtMostOneTrue a0 a1 a2 a3 a4 →
        cyc (a0 || a1 || a2) (a1 || a2 || a3) (a2 || a3 || a4) (a3 || a4 || a0) (a4 || a0 || a1)
          = (a0 || a1) := by decide
    have hunion : ∀ a0 a1 a2 a3 a4 : Bool,
        ((a0 || a1 || a2) || (a1 || a2 || a3) || (a2 || a3 || a4) || (a3 || a4 || a0)
            || (a4 || a0 || a1))
          = (a0 || a1 || a2 || a3 || a4) := by decide
    obtain ⟨g₀, hg₀, he₀⟩ := Finset.exists_mem_eq_inf'
      (admSet_nonempty M (fun v => A₀ v || A₁ v || A₂ v)) (cutWeight M.toBulkGraph)
    obtain ⟨g₁, hg₁, he₁⟩ := Finset.exists_mem_eq_inf'
      (admSet_nonempty M (fun v => A₁ v || A₂ v || A₃ v)) (cutWeight M.toBulkGraph)
    obtain ⟨g₂, hg₂, he₂⟩ := Finset.exists_mem_eq_inf'
      (admSet_nonempty M (fun v => A₂ v || A₃ v || A₄ v)) (cutWeight M.toBulkGraph)
    obtain ⟨g₃, hg₃, he₃⟩ := Finset.exists_mem_eq_inf'
      (admSet_nonempty M (fun v => A₃ v || A₄ v || A₀ v)) (cutWeight M.toBulkGraph)
    obtain ⟨g₄, hg₄, he₄⟩ := Finset.exists_mem_eq_inf'
      (admSet_nonempty M (fun v => A₄ v || A₀ v || A₁ v)) (cutWeight M.toBulkGraph)
    have hv0 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hg₀) v hv
    have hv1 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hg₁) v hv
    have hv2 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hg₂) v hv
    have hv3 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hg₃) v hv
    have hv4 := fun v (hv : M.bdry v = true) => (mem_admSet.mp hg₄) v hv
    have hadm0 : (fun v => cyc (g₀ v) (g₁ v) (g₂ v) (g₃ v) (g₄ v))
        ∈ admSet M (fun v => A₀ v || A₁ v) := by
      rw [mem_admSet]
      intro v hv
      show cyc (g₀ v) (g₁ v) (g₂ v) (g₃ v) (g₄ v) = (A₀ v || A₁ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hpair _ _ _ _ _ (hd v)
    have hadm1 : (fun v => cyc (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₀ v))
        ∈ admSet M (fun v => A₁ v || A₂ v) := by
      rw [mem_admSet]
      intro v hv
      show cyc (g₁ v) (g₂ v) (g₃ v) (g₄ v) (g₀ v) = (A₁ v || A₂ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hpair (A₁ v) (A₂ v) (A₃ v) (A₄ v) (A₀ v) (by
        have := hd v
        unfold AtMostOneTrue at this ⊢
        omega)
    have hadm2 : (fun v => cyc (g₂ v) (g₃ v) (g₄ v) (g₀ v) (g₁ v))
        ∈ admSet M (fun v => A₂ v || A₃ v) := by
      rw [mem_admSet]
      intro v hv
      show cyc (g₂ v) (g₃ v) (g₄ v) (g₀ v) (g₁ v) = (A₂ v || A₃ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hpair (A₂ v) (A₃ v) (A₄ v) (A₀ v) (A₁ v) (by
        have := hd v
        unfold AtMostOneTrue at this ⊢
        omega)
    have hadm3 : (fun v => cyc (g₃ v) (g₄ v) (g₀ v) (g₁ v) (g₂ v))
        ∈ admSet M (fun v => A₃ v || A₄ v) := by
      rw [mem_admSet]
      intro v hv
      show cyc (g₃ v) (g₄ v) (g₀ v) (g₁ v) (g₂ v) = (A₃ v || A₄ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hpair (A₃ v) (A₄ v) (A₀ v) (A₁ v) (A₂ v) (by
        have := hd v
        unfold AtMostOneTrue at this ⊢
        omega)
    have hadm4 : (fun v => cyc (g₄ v) (g₀ v) (g₁ v) (g₂ v) (g₃ v))
        ∈ admSet M (fun v => A₄ v || A₀ v) := by
      rw [mem_admSet]
      intro v hv
      show cyc (g₄ v) (g₀ v) (g₁ v) (g₂ v) (g₃ v) = (A₄ v || A₀ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hpair (A₄ v) (A₀ v) (A₁ v) (A₂ v) (A₃ v) (by
        have := hd v
        unfold AtMostOneTrue at this ⊢
        omega)
    have hadmU : (fun v => g₀ v || g₁ v || g₂ v || g₃ v || g₄ v)
        ∈ admSet M (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v) := by
      rw [mem_admSet]
      intro v hv
      show (g₀ v || g₁ v || g₂ v || g₃ v || g₄ v) = (A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
      rw [hv0 v hv, hv1 v hv, hv2 v hv, hv3 v hv, hv4 v hv]
      exact hunion (A₀ v) (A₁ v) (A₂ v) (A₃ v) (A₄ v)
    have l0 := Finset.inf'_le (cutWeight M.toBulkGraph) hadm0
    have l1 := Finset.inf'_le (cutWeight M.toBulkGraph) hadm1
    have l2 := Finset.inf'_le (cutWeight M.toBulkGraph) hadm2
    have l3 := Finset.inf'_le (cutWeight M.toBulkGraph) hadm3
    have l4 := Finset.inf'_le (cutWeight M.toBulkGraph) hadm4
    have lU := Finset.inf'_le (cutWeight M.toBulkGraph) hadmU
    have hkey := hcut g₀ g₁ g₂ g₃ g₄
    simp only [entropy] at *
    linarith
  have hterm : ∀ (b₀ b₁ b₂ b₃ b₄ : Bool) (X : Region V),
      X = unionSel b₀ b₁ b₂ b₃ b₄ A₀ A₁ A₂ A₃ A₄ →
      entropy M X = (Sw (bmask b₀ b₁ b₂ b₃ b₄) : ℝ) := by
    intro b₀ b₁ b₂ b₃ b₄ X hX
    rw [hX, hreal]
  have e01 := hterm true true false false false (fun v => A₀ v || A₁ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have e12 := hterm false true true false false (fun v => A₁ v || A₂ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have e23 := hterm false false true true false (fun v => A₂ v || A₃ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have e34 := hterm false false false true true (fun v => A₃ v || A₄ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have e40 := hterm true false false false true (fun v => A₄ v || A₀ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have eall := hterm true true true true true (fun v => A₀ v || A₁ v || A₂ v || A₃ v || A₄ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have t012 := hterm true true true false false (fun v => A₀ v || A₁ v || A₂ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have t123 := hterm false true true true false (fun v => A₁ v || A₂ v || A₃ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have t234 := hterm false false true true true (fun v => A₂ v || A₃ v || A₄ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have t340 := hterm true false false true true (fun v => A₃ v || A₄ v || A₀ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  have t401 := hterm true true false false true (fun v => A₄ v || A₀ v || A₁ v)
    (by funext v; simp [unionSel, Bool.or_comm, Bool.or_assoc, Bool.or_left_comm])
  rw [e01, e12, e23, e34, e40, eall, t012, t123, t234, t340, t401] at hcyc
  norm_num [Sw, bmask] at hcyc
