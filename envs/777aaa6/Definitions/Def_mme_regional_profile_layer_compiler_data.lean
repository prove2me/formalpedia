-- Prove2me | Definitions.Def_mme_regional_profile_layer_compiler_data
-- name    : mme_regional_profile_layer_compiler_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-30T21:10:30.220292+00:00
-- url     : https://prove2.me/theorems/eb1a930f-7674-4e52-8aa3-b6e81a4a9b22
-- title:
--   Integer regional profiles, spatial layers, and finite window routing
-- statement:
--   This interface describes the input to a depth-four regional recipe compiler. A packet contains positive regional counts, split counts, three complete-word histograms, a joint table realizing all three histograms with the required grades and coordinatewise CW support, and a nonnegative rate strictly below the explicit regional entropy rate. It also carries admissible reference-address layouts at the common square scales. No extraction stage or recipe is assumed.
--
--   A layer is a finite spatial partition into packets. Its source is the conjunction of the packets' parent-graded frequency windows. Its degree is the sum of their fixed histogram-type degrees and its rate is the sum of their prescribed rates.
--
--   A bridge records a finite array of nonnegative weights with row sums at most one. Exact coordinate-count identities express each incoming complete-word histogram as its replicated cell mass times the weighted child parent-word frequencies. A corresponding finite center identity expresses its central histogram using the same weights. Grade transport is supplied by the physical coordinate layout. Zero-mass cells need no division by their size. These are certificate obligations about integer counts, rationally expressible centers, and coordinate maps; the interface does not assume a window inclusion or the existence of any stages or recipes.
--
--   The compiler theorem constructs the stages from these packets and proves window inclusion from the bridge identities. The definition itself does not supply a feasible numerical AlphaEvolve witness, its coordinate-routing proofs, terminal volume rates, or the final strict exponent surplus.
-- source:
--   Auxiliary input interface for the AlphaEvolve level-four mission, derived from the platform graded step/recipe definitions (99cd2e8f-ea35-448d-a8e9-757f1b42bb0d), fixed-parent-window square-stage theorem (0c054ab2-3215-4bdd-a6ae-2edf3d3dc503), and joint-support histogram theorem (6fb19583-686c-4404-ae5d-b4bff847672b). Application context: Dupont et al., arXiv:2608.16884v1, Sections 2.4 and 4, https://arxiv.org/html/2608.16884v1. This interface is an auxiliary formalization, not a verbatim paper definition.

import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.RegionRate
  MME.DWZProfiledRegional
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MME.ProfileCompiler

/-- Integer profile data, a joint support table, and layouts of its replicated
reference addresses. No extraction stage or recipe is a field. -/
structure Packet (ell : ℕ) where
  regions : ℕ
  regions_pos : 0 < regions
  parent : Fin regions → Fin 3 → ℕ
  total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1))
  n : Fin regions → ℕ
  n_pos : ∀ r, 0 < n r
  m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ
  m_mass : ∀ r, ∑ s, m r s = n r
  mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) regions parent →
    CompleteSplit.CompleteWord ell → ℕ
  mu_mass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (total c.1) c.2)
  joint : Cell (2 * 2 ^ (ell - 1)) regions parent →
    (Fin 3 → CompleteSplit.CompleteWord ell) → ℕ
  joint_mass : ∀ c, ∑ z, joint c z = m c.1 c.2 + m c.1 (complement (total c.1) c.2)
  joint_support : ∀ c z, 0 < joint c z → ∀ r,
    (z 0 r).val + (z 1 r).val + (z 2 r).val = 2
  joint_grade : ∀ c z, 0 < joint c z → ∀ i,
    ∑ r, (z i r).val = (c.2.val i).val
  joint_marginal : ∀ i c w, ∑ z ∈ Finset.univ.filter
    (fun z : Fin 3 → CompleteSplit.CompleteWord ell ↦ z i = w), joint c z = mu i c w
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_strict : rate < regionalRate total n m mu
  address : ∀ k : ℕ, Address (2 * 2 ^ (ell - 1)) regions parent (fun r ↦ k ^ 2 * n r)
  address_valid : ∀ k, address k ∈ RecursiveXHash.target
    (n := fun r ↦ k ^ 2 * n r) (fun r s ↦ k ^ 2 * m r s)

abbrev Packet.Cells {ell : ℕ} (p : Packet ell) :=
  Cell (2 * 2 ^ (ell - 1)) p.regions p.parent

def Packet.size {ell : ℕ} (p : Packet ell) (k : ℕ) : ℕ :=
  lenAt p.n (k ^ 2) * 2 ^ (ell - 1)

def Packet.degree {ell : ℕ} (p : Packet ell) : ℕ :=
  9 * Fintype.card p.Cells * Fintype.card (CompleteSplit.CompleteWord ell)

def Packet.mass {ell : ℕ} (p : Packet ell) (c : p.Cells) : ℕ :=
  p.m c.1 c.2 + p.m c.1 (complement (p.total c.1) c.2)

def Packet.words {ell : ℕ} (p : Packet ell) (k : ℕ)
    (x : ProfiledCW.FineWord (p.size k)) :
    Position (fun r ↦ k ^ 2 * p.n r) → CompleteSplit.CompleteWord ell :=
  ProfiledCW.split (positionsAt p.n (k ^ 2)) rfl x

noncomputable def Packet.center {ell : ℕ} (p : Packet ell) (i : Fin 3)
    (r : Fin p.regions) (w : Fin 2 → CompleteSplit.CompleteWord ell) : ℝ :=
  parentMixture p.total p.n p.m (p.mu i) r w

noncomputable def Packet.observe {ell : ℕ} (p : Packet ell) (k : ℕ)
    (x : ProfiledCW.FineWord (p.size k)) (r : Fin p.regions)
    (w : Fin 2 → CompleteSplit.CompleteWord ell) : ℝ :=
  (Fintype.card {t : Fin (k ^ 2 * p.n r) // ∀ h, p.words k x ⟨r,t,h⟩ = w h} : ℝ) /
    (k ^ 2 * p.n r : ℕ)

noncomputable def Packet.source {ell : ℕ} (p : Packet ell) (eps : ℝ) (k : ℕ) :
    ProfiledCW.Predicate (p.size k) := fun i x ↦
  ParentGraded p.parent (fun r ↦ k ^ 2 * p.n r) i (p.words k x) ∧
    ∀ r w, |p.observe k x r w - p.center i r w| < eps

noncomputable def Packet.histogram {ell : ℕ} (p : Packet ell) (k : ℕ)
    (x : ProfiledCW.FineWord (p.size k)) : p.Cells → CompleteSplit.CompleteWord ell → ℕ :=
  count (fullCell p.total (p.address k)) (p.words k x)

noncomputable def Packet.target {ell : ℕ} (p : Packet ell) (delta : ℝ) (k : ℕ) :
    ProfiledCW.Predicate (p.size k) := fun i x ↦
  Graded p.total i (p.address k) (p.words k x) ∧
    (∀ c, ∑ w, p.histogram k x c w = ∑ w, k ^ 2 * p.mu i c w) ∧
    ∀ c w, |(p.histogram k x c w : ℝ) - ((k ^ 2 * p.mu i c w : ℕ) : ℝ)| ≤
      delta * ((∑ z, k ^ 2 * p.mu i c z : ℕ) : ℝ)

/-- A spatial layer consists of finitely many integer profile packets.
Its coordinate equivalence can depend on the common square scale. -/
structure Layer (ell : ℕ) (N : ℕ → ℕ) where
  parts : ℕ
  packet : Fin parts → Packet ell
  positions : ∀ k, ((j : Fin parts) × Fin ((packet j).size k)) ≃ Fin (N k)

def Layer.piece {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) (k : ℕ)
    (x : ProfiledCW.FineWord (N k)) (j : Fin L.parts) :
    ProfiledCW.FineWord ((L.packet j).size k) :=
  fun r ↦ x (L.positions k ⟨j,r⟩)

noncomputable def Layer.source {ell : ℕ} {N : ℕ → ℕ}
    (L : Layer ell N) (eps : ℝ) (k : ℕ) : ProfiledCW.Predicate (N k) :=
  fun i x ↦ ∀ j, (L.packet j).source eps k i (L.piece k x j)

def Layer.degree {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) : ℕ :=
  ∑ j, (L.packet j).degree

noncomputable def Layer.rate {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) : ℝ :=
  ∑ j, (L.packet j).rate

abbrev Layer.Observations {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) :=
  (j : Fin L.parts) × (Fin (L.packet j).regions ×
    (Fin 2 → CompleteSplit.CompleteWord ell))

noncomputable def Layer.observe {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) (k : ℕ)
    (x : ProfiledCW.FineWord (N k)) (o : L.Observations) : ℝ :=
  (L.packet o.1).observe k (L.piece k x o.1) o.2.1 o.2.2

noncomputable def Layer.center {ell : ℕ} {N : ℕ → ℕ} (L : Layer ell N) (i : Fin 3)
    (o : L.Observations) : ℝ := (L.packet o.1).center i o.2.1 o.2.2

/-- Finite weighted routing of child parent-word frequencies into the preceding
layer's complete-word histogram. The fields are exact coordinate/count/center
identities and grade transport, not stages, recipes, or window inclusions.
Zero-mass cells use zero weights and require no division by their size. -/
structure Bridge {upper lower : ℕ} {N : ℕ → ℕ}
    (A : Layer upper N) (B : Layer lower N) where
  weight : ∀ j : Fin A.parts, (A.packet j).Cells →
    CompleteSplit.CompleteWord upper → B.Observations → ℝ
  weight_nonneg : ∀ j c w o, 0 ≤ weight j c w o
  weight_sum : ∀ j c w, ∑ o, weight j c w o ≤ 1
  count_identity : ∀ k (i : Fin 3) (x : ProfiledCW.FineWord (N k)) j c w,
    ((A.packet j).histogram k (A.piece k x j) c w : ℝ) =
      ((k ^ 2 * (A.packet j).mass c : ℕ) : ℝ) *
        ∑ o, weight j c w o * B.observe k x o
  center_identity : ∀ i j c w, ((A.packet j).mu i c w : ℝ) =
    ((A.packet j).mass c : ℝ) * ∑ o, weight j c w o * B.center i o
  grade_identity : ∀ k i (x : ProfiledCW.FineWord (N k)),
    (∀ j, ParentGraded (B.packet j).parent (fun r ↦ k ^ 2 * (B.packet j).n r) i
      ((B.packet j).words k (B.piece k x j))) →
    ∀ j, Graded (A.packet j).total i ((A.packet j).address k)
      ((A.packet j).words k (A.piece k x j))

end MME.ProfileCompiler


