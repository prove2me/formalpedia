-- Prove2me | solution 1 for Erdos180.quadrangle_uniform_lower_of_prime_power_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:51:10.893491+00:00
-- url     : https://prove2.me/submissions/fba52580-eb49-4217-ac8f-8a16c05f92f7

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Theorems.Thm_Erdos180_symplecticIncidence_card_by_points
import Theorems.Thm_Erdos180_symplecticPoint_card

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticPointsOnLine_card [Finite K]
    (L : SymplecticLine K) :
    Nat.card (SymplecticPointsOnLine K L) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticPointsOnLineEquiv K L)]
  exact Projectivization.card_of_finrank_two K L.1 L.2.1

lemma symplecticIncidence_card_by_lines [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ L : SymplecticLine K,
          SymplecticPointsOnLine K L) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaLines K)
    _ = ∑ L : SymplecticLine K,
          Nat.card (SymplecticPointsOnLine K L) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
      simp_rw [symplecticPointsOnLine_card]
      simp [Nat.card_eq_fintype_card]

lemma symplecticLine_card [Finite K] :
    Nat.card (SymplecticLine K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  have hcounts :
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) =
        Nat.card (SymplecticLine K) * (Nat.card K + 1) :=
    (symplecticIncidence_card_by_points K).symm.trans
      (symplecticIncidence_card_by_lines K)
  have hline : Nat.card (SymplecticPoint K) =
      Nat.card (SymplecticLine K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hcounts
  rw [← hline, symplecticPoint_card]

lemma symplecticIncidence_card [Finite K] :
    Nat.card (SymplecticIncidence K) =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [symplecticIncidence_card_by_points, symplecticPoint_card]
  ring

theorem symplecticQuadrangle_vertex_card [Finite K] :
    Nat.card (QuadrangleVertex K) =
      2 * (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  rw [Nat.card_sum, symplecticPoint_card, symplecticLine_card]
  ring

theorem symplecticQuadrangle_edge_card [Finite K] :
    Nat.card (symplecticQuadrangle K).edgeSet =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [← Nat.card_congr (symplecticIncidenceEquivEdge K),
    symplecticIncidence_card]

end

noncomputable section
open SimpleGraph

theorem quadrangle_density_certificate (q : ℕ) :
    (quadrangleVertexCount q : ℝ) ^ 4 ≤
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 := by
  have hnonneg :
      0 ≤ 32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
        ((q : ℝ) ^ 2 + 1) ^ 3 := by
    positivity
  have hidentity :
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 -
          (quadrangleVertexCount q : ℝ) ^ 4 =
        32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
          ((q : ℝ) ^ 2 + 1) ^ 3 := by
    simp only [quadrangleVertexCount, quadrangleEdgeCount,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  linarith

theorem quadrangle_rpow_density (q : ℕ) :
    (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  apply ((by decide : Odd 3).strictMono_pow.le_iff_le).mp
  have hcubed :
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (quadrangleVertexCount q : ℝ) ^ 4 / 16 := by
    rw [mul_pow,
      ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))
        (-((4 : ℝ) / 3)) 3,
      ← Real.rpow_mul_natCast
        (by exact_mod_cast (Nat.zero_le (quadrangleVertexCount q)))
        ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hcubed]
  nlinarith [quadrangle_density_certificate q]

theorem quadrangleVertexCount_mul_le
    (q t : ℕ) (ht : 1 ≤ t) :
    quadrangleVertexCount (t * q) ≤
      t ^ 3 * quadrangleVertexCount q := by
  have hfirst : t * q + 1 ≤ t * (q + 1) := by
    nlinarith
  have hsecond : (t * q) ^ 2 + 1 ≤ t ^ 2 * (q ^ 2 + 1) := by
    nlinarith [sq_nonneg (t - 1)]
  unfold quadrangleVertexCount
  calc
    2 * (t * q + 1) * ((t * q) ^ 2 + 1) ≤
        2 * (t * (q + 1)) * (t ^ 2 * (q ^ 2 + 1)) := by
      gcongr
    _ = t ^ 3 * (2 * (q + 1) * (q ^ 2 + 1)) := by
      ring

lemma free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa using hbound

lemma nat_le_pow_of_two_le
    {t : ℕ} (ht : 2 ≤ t) (j : ℕ) : j ≤ t ^ j := by
  exact (Nat.lt_pow_self (show 1 < t by omega)).le

theorem quadrangleVertexCount_parameter_lt (q : ℕ) :
    q < quadrangleVertexCount q := by
  unfold quadrangleVertexCount
  nlinarith [sq_nonneg q]

theorem quadrangle_prime_power_bracketing
    {t n : ℕ} (ht : 2 ≤ t)
    (hn : quadrangleVertexCount t ≤ n) :
    ∃ j : ℕ, 0 < j ∧
      quadrangleVertexCount (t ^ j) ≤ n ∧
      n < t ^ 3 * quadrangleVertexCount (t ^ j) := by
  let P : ℕ → Prop := fun j =>
    quadrangleVertexCount (t ^ j) ≤ n
  let j := Nat.findGreatest P (n + 1)
  have hone : P 1 := by
    simpa [P] using hn
  have hjfit : P j :=
    Nat.findGreatest_spec (P := P)
      (show 1 ≤ n + 1 by omega) hone
  have hjpositive : 0 < j := by
    have hle : 1 ≤ j := Nat.le_findGreatest
      (show 1 ≤ n + 1 by omega) hone
    omega
  have hjn : j ≤ n := by
    have hpow := nat_le_pow_of_two_le ht j
    have hvertex := quadrangleVertexCount_parameter_lt (t ^ j)
    change quadrangleVertexCount (t ^ j) ≤ n at hjfit
    omega
  have hnext : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (P := P)
      (show j < j + 1 by omega)
      (show j + 1 ≤ n + 1 by omega)
  have hnnext :
      n < quadrangleVertexCount (t * t ^ j) := by
    have h := Nat.lt_of_not_ge hnext
    change n < quadrangleVertexCount (t ^ (j + 1)) at h
    simpa [pow_succ, Nat.mul_comm] using h
  have hgap := quadrangleVertexCount_mul_le (t ^ j) t
    (show 1 ≤ t by omega)
  exact ⟨j, hjpositive, hjfit, lt_of_lt_of_le hnnext hgap⟩

theorem quadrangle_extremal_lower_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hfree : forbidden.Free (symplecticQuadrangle K)) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber
        (quadrangleVertexCount (Nat.card K)) forbidden := by
  classical
  letI : Fintype (QuadrangleVertex K) := Fintype.ofFinite _
  have hvertex : Fintype.card (QuadrangleVertex K) =
      quadrangleVertexCount (Nat.card K) := by
    rw [← Nat.card_eq_fintype_card, symplecticQuadrangle_vertex_card]
    rfl
  calc
    quadrangleEdgeCount (Nat.card K) =
        (symplecticQuadrangle K).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        symplecticQuadrangle_edge_card]
      rfl
    _ ≤ SimpleGraph.extremalNumber
          (Fintype.card (QuadrangleVertex K)) forbidden :=
      SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    _ = SimpleGraph.extremalNumber
          (quadrangleVertexCount (Nat.card K)) forbidden := by
      rw [hvertex]

theorem quadrangle_extremal_lower_padded_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (hfree : forbidden.Free (symplecticQuadrangle K))
    {n : ℕ} (hn : quadrangleVertexCount (Nat.card K) ≤ n) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber n forbidden := by
  exact (quadrangle_extremal_lower_of_free K forbidden hfree).trans
    (extremalNumber_monotone_of_no_isolated forbidden hneighbors hn)

theorem quadrangle_manuscript_scaled_density_of_gap
    (q n : ℕ)
    (hgap : n ≤ 27 * quadrangleVertexCount q) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  have hreal :
      (n : ℝ) ≤ (27 : ℝ) * (quadrangleVertexCount q : ℝ) := by
    exact_mod_cast hgap
  calc
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        (n : ℝ) ^ ((4 : ℝ) / 3) ≤
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        ((27 : ℝ) * (quadrangleVertexCount q : ℝ)) ^
          ((4 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hreal (by positivity))
        (by positivity)
    _ = (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hcancel :
          (27 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ ((4 : ℝ) / 3) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 27)]
        norm_num
      calc
        ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
            ((27 : ℝ) ^ ((4 : ℝ) / 3) *
              (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) =
          (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            ((27 : ℝ) ^ (-((4 : ℝ) / 3)) *
              (27 : ℝ) ^ ((4 : ℝ) / 3)) *
                (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
          ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (quadrangleEdgeCount q : ℝ) := quadrangle_rpow_density q

end

end Erdos180

open Erdos180
open SimpleGraph

theorem solution
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.Free (symplecticQuadrangle (GaloisField t j)))
    {n : ℕ} (hn : quadrangleVertexCount t ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
  obtain ⟨j, hj, hfit, hgap⟩ :=
    quadrangle_prime_power_bracketing ht hn
  let K := GaloisField t j
  have hcard : Nat.card K = t ^ j :=
    GaloisField.card t j (Nat.ne_of_gt hj)
  have hfitK : quadrangleVertexCount (Nat.card K) ≤ n := by
    simpa [hcard] using hfit
  have havoid : forbidden.Free (symplecticQuadrangle K) :=
    hfree j hj
  have hedge := quadrangle_extremal_lower_padded_of_free K
    forbidden hneighbors havoid hfitK
  have hedge' :
      (quadrangleEdgeCount (t ^ j) : ℝ) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
    exact_mod_cast (show quadrangleEdgeCount (t ^ j) ≤
      SimpleGraph.extremalNumber n forbidden by
        simpa [hcard] using hedge)
  have hfactor :
      t ^ 3 * quadrangleVertexCount (t ^ j) ≤
        27 * quadrangleVertexCount (t ^ j) :=
    Nat.mul_le_mul_right (quadrangleVertexCount (t ^ j)) htgap
  have hgap27 : n ≤ 27 * quadrangleVertexCount (t ^ j) :=
    (Nat.le_of_lt hgap).trans hfactor
  exact (quadrangle_manuscript_scaled_density_of_gap
    (t ^ j) n hgap27).trans hedge'
