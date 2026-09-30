-- Prove2me | Theorems.Thm_Hirsch_alternating_complement_exchange_routes
-- name    : Hirsch.alternating_complement_exchange_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-18T22:09:39.588882+00:00
-- url     : https://prove2.me/theorems/640da3d5-6767-4a08-bdbc-70be357466af
-- title:
--   Construct short single-label exchange routes for alternating complements in both parity phases
-- statement:
--   Let h,k enumerate two r-element subsets of the m ordered labels 0,...,m-1. Assume each enumeration is strictly increasing and its values have alternating parity, with either starting parity permitted independently. Construct a route of length at most 2r+1 between their label sets. Every intermediate set has r labels in the same universe and an explicitly witnessed increasing alternating-parity enumeration. Every successive pair is distinct and has exactly r-1 common labels. The selected complements have cardinality m-r, are distinct at every step, and share exactly m-r-1 labels. The complete path is a conclusion, not a hypothesis; stationary transitions are removed. The cases r=0, r=m, m=0, and equal endpoints are included, without a shortestness assertion. This is an order-only combinatorial route theorem, not yet a formally composed original-polytope route or unrestricted Polynomial Hirsch theorem.
-- source:
--   New complement-coordinate packing argument following accepted original moment vertex/release interfaces #299/#298 and the owned parity-to-geometry packet #302. The new source proves all of its finite combinatorial helpers directly; it does not submit any old public target again or assume a short admissible exchange path. The elementary stationary-step compression follows the same recursion pattern as the accepted finite-ascent path helper in #301, without importing its target. Classical cyclic-polytope/Gale-evenness geometry is credited; A.M. Maksimenko, The diameter of the ridge-graph of a cyclic polytope, Discrete Mathematics and Applications 19(1), 47-53 (2009), DOI10.1515/DMA.2009.003, gives sharper classical diameter results. No historical-first or best-known diameter claim. This combinatorial theorem is distinct from #300 separated-pair geometric routes and #302 the numerical/parity catalogue equivalence.

import Mathlib
set_option autoImplicit false

theorem Hirsch.alternating_complement_exchange_routes (m r : ℕ) (h k : Fin r → ℕ)
    (hh : StrictMono h) (hk : StrictMono k)
    (hhm : ∀ i, h i < m) (hkm : ∀ i, k i < m)
    (hphase : ∃ b : ℕ, b < 2 ∧ ∀ i, h i % 2 = (b + i.val) % 2)
    (kphase : ∃ b : ℕ, b < 2 ∧ ∀ i, k i % 2 = (b + i.val) % 2) :
    ∃ L : ℕ, L ≤ 2*r+1 ∧ ∃ p : ℕ → Finset ℕ,
      p 0 = Finset.univ.image h ∧ p L = Finset.univ.image k ∧
      (∀ t, t ≤ L → p t ⊆ Finset.range m ∧ (p t).card = r ∧
        (Finset.range m \ p t).card = m-r ∧
        ∃ a : Fin r → ℕ, StrictMono a ∧ (∀ i, a i < m) ∧
          (∃ b : ℕ, b < 2 ∧ ∀ i, a i % 2 = (b + i.val) % 2) ∧
          Finset.univ.image a = p t) ∧
      (∀ t, t < L → p t ≠ p (t+1) ∧ (p t ∩ p (t+1)).card + 1 = r ∧
        (Finset.range m \ p t) ≠ (Finset.range m \ p (t+1)) ∧
        ((Finset.range m \ p t) ∩ (Finset.range m \ p (t+1))).card + 1 = m-r) := by sorry
